module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle188
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationContinuous
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.local_holomorphic_exponential_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exp_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.exp_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exp_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem rank_eq_unif_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (M : LB A.left) (g : ℕ) (u : HolUnif A M g), IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → D.g = g := by
  intro E _ _ _ H L _ _ D σ A _ φ M g u hp h1 h2
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  obtain ⟨Mσ, -⟩ := GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre (Sp (𝓞 L)) D.t.G L (𝟙 _) D.B.carrier D.MB σ
  have hp' : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) φ := by
    rwa [Category.comp_id]
  obtain ⟨e, -⟩ := GlobalTheory.T.tangent_space_equiv_hol_unif _ D.t.G _ _ Mσ A φ M g u hp' h1 h2
  have hf : Module.finrank ℂ (Fibre σ D.B.carrier) = g := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have hr : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank (𝓞 L) D.B.carrier :=
    GroundTheory.Heights₂.Heights.FibreMahlerForms.finrank_fibreSpace D.B.metric σ
  have hq : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank ℂ (Fibre σ D.B.carrier) :=
    (FibreSpace.equiv D.B.metric σ).symm.finrank_eq
  change Module.finrank (𝓞 L) D.B.carrier = g
  rw [← hr, hq, hf]

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem gramAt_continuous_anTop : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H :=
  @PositivityTheory.Xgn.torus_uniformization_continuous

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem stalk_key {K K' : Type} [Field K] [Field K'] (w : Spec (CommRingCat.of K) ⟶ X)
    (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K') (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') :
    ∃ hc : centre w' = centre w, X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo w' = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := by
  have hl : IsLocalHom (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom := by
    refine ⟨fun b hb => ?_⟩
    have h1 : IsUnit (f ((Scheme.stalkClosedPointTo w).hom b)) := hb
    have h2 : IsUnit ((Scheme.stalkClosedPointTo w).hom b : K) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo w).hom b h2
  have e2 : w' = Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))) := by
    rw [← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hc0 : (Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))))
        (IsLocalRing.closedPoint (CommRingCat.of K')) =
      w (IsLocalRing.closedPoint (CommRingCat.of K)) :=
    closedPoint_specMap_fromSpecStalk (R := CommRingCat.of K') _ _
  have key0 := stalkSpecializes_stalkClosedPointTo _ _ hc0
  clear e
  subst e2
  exact ⟨hc0, key0⟩

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_of_eq (M : LieModel G ξ E) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c) (a : E)
    (v : epsAt (R := X.presheaf.stalk c) (X.fromSpecStalk c) ⟶ G) (hv : M.Extends ⟨c, h⟩ a v)
    {K : Type} [CommRing K] (φ : X.presheaf.stalk c' ⟶ CommRingCat.of K) :
    ∃ (h' : genPt ξ ⤳ c') (v' : epsAt (R := X.presheaf.stalk c') (X.fromSpecStalk c') ⟶ G),
      M.Extends ⟨c', h'⟩ a v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v'.left =
        Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫ φ).hom)) ≫
          v.left := by
  subst hc
  refine ⟨h, v, hv, ?_⟩
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem valAt_field_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (K K' : Type) [Field K] [Field K'] (w : Sp K ⟶ X) (f : K →+* K') (a : Li) (v : epsAt w ⟶ G), M.ValAt w a v → M.ValAt (spMap f ≫ w) a (GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps f w ≫ v) := by
  intro X Ω _ ξ G _ Li _ _ M K K' _ _ w f a v hv
  obtain ⟨h, v₀, hE, hl⟩ := hv
  obtain ⟨hc, key⟩ := stalk_key w (spMap f ≫ w) f rfl
  obtain ⟨h', v', hE', hl'⟩ := extends_of_eq M hc h a v₀ hE (Scheme.stalkClosedPointTo (spMap f ≫ w))
  refine ⟨h', v', hE', ?_⟩
  refine Eq.trans ?_ hl'.symm
  rw [key, Over.comp_left, hl]
  simp only [GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps, Over.homMk_left]
  have e1 : spMap (dualMap f) ≫ Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w).hom)) =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom)) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← dualMap_comp']
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ v₀.left) e1)

end GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

theorem homAt_comp' {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetSubstP_mk_X {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetCopy_mkX {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (j : Fin d) :
    jetCopy (S := S) d m i (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_psIn {S : Type} [CommRing S] {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n')
    (f : MvPowerSeries (Fin n × Fin d) S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  unfold psIn

  rw [MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h
    simpa using hf
  · rfl

end GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf


open PeOne in
theorem peG_act_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val (peG t x d g.x g.e (p + m + 1) ![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (homAt x (jq w p m)).left z J = 1 := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w m hp z J hJ
  have hring : (jq w p m).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
      (![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j),
        fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) q.1 q.2) =
      ((jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2))).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
        (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k)
          q.1 q.2) := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun q => ?_)
    obtain ⟨a, j⟩ := q
    show _ = _
    simp only [AlgHom.comp_apply]
    refine Eq.trans (congrArg (jq w p m) (jetSubstP_mk_X _ _ _)) ?_
    refine Eq.trans ?_ (congrArg (fun u => jq w p m (jetCopy d (p + m + 1) (1 : Fin 2) u)) (jetSubstP_mk_X _ _ _)).symm
    fin_cases a
    · have h0 := GlobalTheory.T.germ_frobenius_torsion_jet E H hstar X0 t k p x d g w m hp j
      have hc := constantCoeff_psIn (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j) (g.B.A.const _ _)
      simp [hc, h0]
    · simp [jetCopy_mkX]
  have hcomp := congrArg (fun f => (homAt x f).left) hring
  simp only [homAt_comp', Over.comp_left] at hcomp
  refine (val_pull hJ _ _ _).trans ?_
  rw [hcomp]
  refine (val_pull hJ _ _ _).symm.trans ?_
  exact (val_corr hJ (g.axes _).1 _).trans (val_one _)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section


theorem _root_.GlobalTheory.T.HTChartExists_holds : GlobalTheory.CompanionTheory.Ar.BT.HTChartExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | exact GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_fibre_projective_embedding : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | exact GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_resolution_generic_fibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ObjAt

theorem exists_obj_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (f : X ⟶ Y.X) (t : SAB H X) (_ : SABMap t Y.t f) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ Xo.XF c), ξ ≫ f = x ≫ Y.j → ∃ (s : Sp Ω ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), Nonempty (SABMap o.t t ξ) := by
  intro E _ _ _ H D l Xo c O _ β Y X f t h Ω _ ξ x hx
  obtain ⟨o, ⟨mP⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l)
    (RingHom.id _) _ _ _ (x ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) x rfl rfl (by rw [show spMap (RingHom.id (KA l)) = 𝟙 (Sp (KA l)) by simp [spMap], Category.comp_id]) Y.oF
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t o.t Y.j x Y.m mP.toSABMap
  have n' : SABMap o.t Y.t (ξ ≫ f) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n hx.symm
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t t o.t f ξ h n'
  exact ⟨_, o, ⟨k⟩⟩

end GlobalTheory.CompanionTheory.Ar.ObjAt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_generic_weil_pairing : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S X : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (f : S ⟶ X) (_ : SABMap o.t t f) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → FullTorsion t.G (ξ₀ ≫ f) n → (∃ ζ : Ω, IsPrimitiveRoot ζ n) → ∃ e, GenWeil t.G t.PP.L (ξ₀ ≫ f) n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | exact GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj <;> assumption)
end
