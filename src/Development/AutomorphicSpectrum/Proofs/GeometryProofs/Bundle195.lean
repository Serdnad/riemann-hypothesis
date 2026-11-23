module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle010
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle004
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IsPrincipalIffOfBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle193
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle192
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangents
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.intersection_family_flat_herm : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_eval_at_local_ring : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER), IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER, (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧ (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧ Submodule.span R (Set.range ev) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_val | exact GlobalTheory.CompanionTheory.Ar.lieLat_val | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_tate_weil_open_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion x] (κ : FractionRing R ≃+* Ω), spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x n i → ∀ (L₀ : Type) [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E), (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) → ∀ (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E), y ^ n = 1 → (∀ (t : T) (g : Over.mk ξ ⟶ G), spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → κ (algebraMap R _ (χ t : R)) = e y g) → Γ.IsHT i M₀ n χ w₀ → (∀ v, w (j v) = κ (algebraMap R _ (w₀ v))) → ∀ q : Cpt ξ, q.1 ∈ Set.range x → M.IsHTAt L n y q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | exact GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.tower_i5_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1))) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R → (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | exact GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_gram_complex_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj | exact GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

open PositivityTheory.Xgf.isogeny_decomposition_product in

theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SingVal

open LiePull LieTangent

section Abstract

open MonObj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {Ω : Type} [Field Ω] {L V : Type} [AddCommGroup L] [Module Ω L]
  [AddCommGroup V] [Module ℂ V] {ξ : Sp Ω ⟶ S} {z : Sp ℂ ⟶ S}

def extSub (W : Subring Ω) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ) (N : LieModel G ξ L) : Submodule W L where
  carrier := {e | ∃ v, Ext W.subtype x N e v}
  add_mem' := fun ⟨_, hv⟩ ⟨_, hv'⟩ => ⟨_, hv.mul hx hv'⟩
  zero_mem' := ⟨_, Ext.zero hx⟩
  smul_mem' c _ := fun ⟨_, hv⟩ => ⟨_, hv.smul c⟩

theorem exists_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hz : spMap φ ≫ x = z) (N : LieModel G ξ L)
    (Nz : LieModel G z V) :
    ∃ val : L → V, ∀ e v, Ext W.subtype x N e v → Nz.pt (val e) = epsBase φ hz ≫ v := by
  classical
  have key : ∀ e, ∃ w, ∀ v, Ext W.subtype x N e v → Nz.pt w = epsBase φ hz ≫ v := by
    intro e
    by_cases h : ∃ v, Ext W.subtype x N e v
    · obtain ⟨v, hv⟩ := h
      obtain ⟨w, hw⟩ := Nz.onto _ (isTanAt_base φ hz hv.1)
      exact ⟨w, fun v' hv' => by rw [hw, hv.unique Subtype.val_injective hv']⟩
    · exact ⟨0, fun v hv => (h ⟨v, hv⟩).elim⟩
  choose val hval using key
  exact ⟨val, hval⟩

theorem exists_lat_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ)
    (hz : spMap φ ≫ x = z) (N : LieModel G ξ L) (Nz : LieModel G z V) :
    ∃ (Lm : Submodule W L) (val : L → V), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧
      (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧
      ∀ e v, Ext W.subtype x N e v → e ∈ Lm ∧ Nz.pt (val e) = epsBase φ hz ≫ v := by
  obtain ⟨val, hval⟩ := exists_val W φ hz N Nz
  refine ⟨extSub W hx N, val, ?_, ?_, ?_, fun e v h => ⟨⟨v, h⟩, hval e v h⟩⟩
  · apply Nz.inj
    rw [hval 0 1 (Ext.zero hx), LieModel.pt_zero, comp_one]
  · rintro e ⟨v, hv⟩ e' ⟨v', hv'⟩
    apply Nz.inj
    rw [hval _ _ (hv.mul hx hv'), Nz.add, hval _ _ hv, hval _ _ hv', comp_mul]
  · rintro a e ⟨v, hv⟩
    apply Nz.inj
    have h1 := hval _ _ (hv.smul a)
    refine h1.trans ?_
    rw [LieModel.pt_smul, hval _ _ hv]
    have e1 : epsBase φ hz ≫ epsScale x a = epsScale z (φ a) ≫ epsBase φ hz := base_scale φ hz a
    have e2 : LieEx.hom x (a • (LinearMap.id : W →ₗ[W] W)) = epsScale x a := rfl
    rw [e2, ← Category.assoc, e1, Category.assoc]

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C)
    {T : Scheme.{0}} (t : Sp (DualNumber A) ⟶ T) :
    spMap (dualMap (b.comp a)) ≫ t = spMap (dualMap b) ≫ spMap (dualMap a) ≫ t := by
  rw [← dualMap_comp]
  exact (congrArg (· ≫ t) (spec_comp (dualMap a) (dualMap b)).symm).trans (Category.assoc _ _ _)

theorem assoc_three {P Q R T U : Scheme.{0}} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ U) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

theorem ext_of_tan {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] {f : X' ⟶ S} {ψ : G'.left ⟶ G.left}
    (hG : IsGrpPullback G' G f ψ) {A B : Type} [CommRing A] [CommRing B] {g : A →+* Ω} {y : Sp B ⟶ X'} (σ : B →+* A)
    {h : B →+* Ω} {x : Sp A ⟶ S} (hxy : x = (spMap σ ≫ y) ≫ f) (hσ : g.comp σ = h) {N : LieModel G ξ L} {e : L}
    {v : epsAt y ⟶ G'} (hv : IsTanAt G' y v)
    (he : (N.pt e).left = spMap (dualMap h) ≫ v.left ≫ ψ) :
    ∃ u : epsAt x ⟶ G, Ext g x N e u ∧ u.left = spMap (dualMap σ) ≫ v.left ≫ ψ := by
  subst hxy
  subst hσ
  refine ⟨LieMove.pushEps hG (epsBase σ rfl ≫ v), ⟨(LieMove.tan_iff hG _).1 (isTanAt_base σ rfl hv), ?_⟩,
    Category.assoc _ _ _⟩
  refine he.trans ?_
  have e1 : spMap (dualMap (g.comp σ)) = spMap (dualMap g) ≫ spMap (dualMap σ) := by
    rw [← dualMap_comp]
    exact (spec_comp _ _).symm
  rw [e1, Category.assoc]
  rfl

end Abstract

theorem value_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) → (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) → (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) → (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) → spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f → ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i ι W φ z₁ z₂ σ₁ σ₂ hgen hι hσ₁ hσ₂ hφ₁ hφ₂ hxx
    Vz _ _ MR
  have hG := 𝔐.m.cart
  have hG₀ := 𝔐₀.m.cart
  have s₁ : W.subtype.comp σ₁ = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ := RingHom.ext hσ₁
  have s₂ : W.subtype.comp σ₂ = i.comp (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩) := RingHom.ext hσ₂
  have t₁ : φ.comp σ₁ = (Scheme.stalkClosedPointTo z₁).hom := RingHom.ext hφ₁
  have t₂ : φ.comp σ₂ = (Scheme.stalkClosedPointTo z₂).hom := RingHom.ext hφ₂
  obtain ⟨x, hx₁⟩ : ∃ x : Sp W ⟶ Y.X, x = (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁)) ≫ 𝔐.f := ⟨_, rfl⟩
  have hx₂ : x = (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂)) ≫ 𝔐₀.f := by
    rw [hx₁, Category.assoc, Category.assoc, hxx]
  have hx : spMap W.subtype ≫ x = 𝔐.ξ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, s₁]
    exact congrArg (· ≫ 𝔐.f) (spec_genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩)
  have hz : spMap φ ≫ x = z₁ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, t₁]
    exact congrArg (· ≫ 𝔐.f) (spec_centre z₁)
  obtain ⟨Lm, val, h0, hadd, hsm, hext⟩ := exists_lat_val W φ hx hz (LieMove.pushModel hG 𝔐.M)
    (LieMove.pushModel hG MR)
  refine ⟨Lm, val, h0, hadd, hsm, ?_, ?_⟩
  · intro e v hv
    obtain ⟨h, v', hv', hl⟩ := hv
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := e) hG σ₁ hx₁ s₁ hv'.1
      (by
        show (𝔐.M.pt e).left ≫ _ = _
        rw [hv'.2]
        exact Category.assoc _ _ _)
    obtain ⟨hm, hpt⟩ := hext e u hu
    refine ⟨hm, LieMove.pushEps_inj hG (Eq.trans ?_ hpt.symm)⟩
    have e3 : v.left = spMap (dualMap φ) ≫ spMap (dualMap σ₁) ≫ v'.left := by
      rw [hl, ← t₁]
      exact spMap_dual_comp _ _ _
    apply Over.OverMorphism.ext
    show v.left ≫ _ = spMap (dualMap φ) ≫ u.left
    rw [hul, e3]
    exact assoc_three _ _ _ _
  · intro e₀ v₀ hv
    obtain ⟨h, v', hv', hl⟩ := hv
    have hι' := (hι e₀ (ι e₀)).2 rfl
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := ι e₀) hG₀ σ₂ hx₂ s₂ hv'.1
      (by
        show (𝔐.M.pt (ι e₀)).left ≫ _ = _
        rw [hι', hv'.2, spMap_dual_comp]
        exact congrArg (_ ≫ ·) (Category.assoc _ _ _))
    obtain ⟨hm, hpt⟩ := hext _ u hu
    refine ⟨hm, ?_⟩
    have e3 : v₀.left = spMap (dualMap φ) ≫ spMap (dualMap σ₂) ≫ v'.left := by
      rw [hl, ← t₂]
      exact spMap_dual_comp _ _ _
    refine (congrArg (fun q => q.left) hpt).trans ?_
    show spMap (dualMap φ) ≫ u.left = _
    rw [hul, e3]
    exact (assoc_three _ _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.SingVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem isPrincipal_iff_of_sabMap_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  exact @CoverDenseAlt.isPrincipal_iff_of_base_change

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.proper_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | exact GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.gaga_line_generator_complex : GagaSections → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] [Algebra ℂ Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap ℂ Ω) → IsCptGen ξ → ConstClosed ℂ Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap (RingHom.id ℂ) → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s (RingHom.id ℂ) ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap (RingHom.id ℂ) → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C | exact GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.component_complex_point_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (n : ℕ) (v : Fin n → Z.V) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y) (w : Fin n → (epsAt y ⟶ Y.t.G)), Function.Injective β → (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ Y.s = spMap (σ.comp β) → (Z.eig τ).IsFrameAt v ⟨centre y, h⟩ → (∀ i, Z.M.ValAt y (v i) (w i)) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | exact GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value <;> assumption)
end
