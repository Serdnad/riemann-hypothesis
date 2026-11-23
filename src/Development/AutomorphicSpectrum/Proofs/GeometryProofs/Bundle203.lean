module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle199
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GramMatrixTwistedLieModels
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle202
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle200
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle198
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle201
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.VanDescent

theorem exists_closed_mem_notMem : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), LocallyOfFiniteType p → ∀ (U O : Y.Opens), ¬ U ≤ O → ∃ z : Y, IsClosed ({z} : Set Y) ∧ z ∈ U ∧ z ∉ O := by
  intro F _ Y p hp U O hUO
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hzU, hzO⟩ := Set.not_subset.1 hUO
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (O : Set Y)ᶜ)
    ⟨z, hzU, hzO⟩ (U.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
  exact ⟨y, hc, hy, hy'⟩

theorem secVal_eq_zero_of_le {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ}
    {B : LB Y} {O : Y.Opens} (s : B.Sec) (hs : nonzeroLocus s ≤ O) (i : B.ι) (y : CxPts p σ)
    (hy : y ∉ ptsIn p σ O) : secVal p σ s i y = 0 := by
  by_contra h
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · exact hy (ptsIn_mono hs ((secVal_ne_zero_iff s hi).1 h))
  · exact h (by rw [secVal_apply]; exact ev_of_notMem hi _)

theorem vanish_descent : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  intro F _ Y p σ hp B hB O x hx
  let J := {z : Y // IsClosed ({z} : Set Y) ∧ z ∉ O}
  have hpt := fun j : J => GlobalTheory.CompanionTheory.Ar.ClosedPt.exists_residue_eval F Y p σ hp B hB j.1 j.2.1
  choose K instF instA instFD e he_smul he_ne he_pt using hpt
  let G : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    Submodule.span ℂ {f | ∃ s : B.Sec, nonzeroLocus s ≤ O ∧ secVal p σ s = f}
  let Z : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    { carrier := {v | ∀ i y, y ∉ ptsIn p σ O → v i y = 0}
      add_mem' := fun {u v} hu hv i y hy => by simp [hu i y hy, hv i y hy]
      zero_mem' := fun i y _ => rfl
      smul_mem' := fun c v hv i y hy => by simp [hv i y hy] }
  have hGZ : G ≤ Z := Submodule.span_le.2 (by
    rintro _ ⟨s, hs, rfl⟩ i y hy
    exact secVal_eq_zero_of_le s hs i y hy)
  have key : ∀ (n : ℕ) (b : Fin n → B.Sec) (d : Fin n → ℂ) (g : B.ι → CxPts p σ → ℂ), g ∈ G →
      (∑ l, d l • secVal p σ (b l) + g) ∈ Z → (∑ l, d l • secVal p σ (b l) + g) ∈ G := by
    intro n
    induction n with
    | zero => intro b d g hg _; simpa using hg
    | succ m ih =>
      intro b d g hg hv
      by_cases H : ∀ a : Fin (m + 1) → F,
          (∀ j, ∑ l, algebraMap F (K j) (a l) * e j (b l) = 0) → a = 0
      · have hz : ∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ →
            ∑ l, d l * τ (e j (b l)) = 0 := by
          intro j τ hτ
          obtain ⟨y, i, hyz, hy⟩ := he_pt j τ hτ
          have hyO : y ∉ ptsIn p σ O := fun h => j.2.2 (hyz ▸ mem_ptsIn.1 h)
          have h1 := hv i y hyO
          have h2 := hGZ hg i y hyO
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero,
            hy] at h1
          exact h1
        have hd : d = 0 := GlobalTheory.CompanionTheory.Arith.DedekindDescent.linIndep_descent F σ J K (Fin (m + 1)) (fun l j => e j (b l)) H d hz
        subst hd
        simpa using hg
      · push Not at H
        obtain ⟨a, ha0, ha⟩ := H
        have hes : ∀ j, e j (∑ l, algX p ⊤ (a l) • b l) = 0 := fun j => by

          simp only [map_sum, he_smul]
          exact ha0 j
        have hsO : nonzeroLocus (∑ l, algX p ⊤ (a l) • b l) ≤ O := by
          by_contra h
          obtain ⟨z, hzc, hzs, hzO⟩ := exists_closed_mem_notMem F Y p hp _ O h
          exact he_ne ⟨z, hzc, hzO⟩ _ hzs (hes _)
        have hsG : secVal p σ (∑ l, algX p ⊤ (a l) • b l) ∈ G :=
          Submodule.subset_span ⟨_, hsO, rfl⟩
        have hsv : secVal p σ (∑ l, algX p ⊤ (a l) • b l) = ∑ l, σ (a l) • secVal p σ (b l) := by

          simp only [map_sum, secVal_smul]
        rw [hsv] at hsG
        obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 ha
        have hσ : σ (a l₀) ≠ 0 := (map_ne_zero σ).2 hl₀
        obtain ⟨c, hc⟩ : ∃ c, c = d l₀ * (σ (a l₀))⁻¹ := ⟨_, rfl⟩
        have hdc : d l₀ = c * σ (a l₀) := by rw [hc, inv_mul_cancel_right₀ hσ]
        have heq : ∑ l, d l • secVal p σ (b l) + g =
            ∑ i, (d (l₀.succAbove i) - c * σ (a (l₀.succAbove i))) •
              secVal p σ (b (l₀.succAbove i)) + (g + c • ∑ l, σ (a l) • secVal p σ (b l)) := by
          rw [Fin.sum_univ_succAbove _ l₀, Fin.sum_univ_succAbove (fun l => σ (a l) • _) l₀]
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdc]
          module
        rw [heq] at hv ⊢
        exact ih _ _ _ (G.add_mem hg (G.smul_mem c hsG)) hv
  have hxspan : x ∈ Submodule.span ℂ (Set.range (SecC.of p σ : B.Sec → SecC p σ B)) :=
    by rw [SecC.span_range_of (p := p) (σ := σ) (B := B)]; exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hxspan
  choose b hb using fun i => (g i).2
  have hval : SecC.val x = ∑ l, f l • secVal p σ (b l) + 0 := by

    rw [← hfg, add_zero, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l, SecC.val_of]
  have hxZ : SecC.val x ∈ Z := hx
  rw [hval] at hxZ
  have hmem := key n b f 0 G.zero_mem hxZ
  rw [← hval] at hmem
  obtain ⟨m, as, ss, hss⟩ := Submodule.mem_span_set'.1 hmem
  choose t ht1 ht2 using fun j => (ss j).2
  exact ⟨m, as, t, ht1, by rw [← hss]; exact Finset.sum_congr rfl fun j _ => by rw [ht2]⟩

end GlobalTheory.CompanionTheory.VanDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.torsion_section_eq_of_connected : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | exact GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.intersection_family_multilinear : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_eval_fraction_field : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | exact GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric


theorem _root_.GlobalTheory.T.lattice_frame_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.lattice_regular_at_local_point : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | exact GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_dominant_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∃ j : V →+ V', (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) ∧ (∀ (a : Ω) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | exact GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem codim_one_gram_twist_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ :=
  PositivityTheory.UnitarySelfGeneration.gram_matrix_twisted_lie_models

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.gaga_line_generator_embedding : GagaSections → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] [Algebra K Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap K Ω) → IsCptGen ξ → ConstClosed K Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap σ → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s σ ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat | exact GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.component_specialization_lattice_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_tate_free_flag_lattice_upper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → (∀ s, Module.Projective (chartRing o (mseg y) s.1) (Dc s).om' ∧ ∀ σ : E →+* Ω, Module.Projective (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) ∧ (∀ σ : E →+* Ω, ∃ d : Ω, ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) ∧ ∃ κ : Ω, IsCp p κ ∧ ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, κ ∈ chartRing o (mseg y) s.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.family_proj | exact GlobalTheory.CompanionTheory.Ar.HT.family_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.family_proj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.frame_at_component_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes <;> assumption)
end
