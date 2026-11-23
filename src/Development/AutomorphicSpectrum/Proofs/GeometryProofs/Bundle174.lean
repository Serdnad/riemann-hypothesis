module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle168
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.holomorphic_points_of_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts | exact GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.det_lattice_flag_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor | exact GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor | (intros; apply GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.coords_added_projective : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks | exact GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem cls_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  intro X Ω _ ξ K _ J y G _ Li _ _ M V r b₀ m i a e₀ _hb₀ hS hD p c hc
  obtain ⟨b, π, hf, hfr, hm, hπ, hr⟩ := hS p

  have hker : flagStep Ω b₀ i ≤ LinearMap.ker (π i) := by
    rw [← hf]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have hkill : ∀ (e : Li) (t : Ω), e - t • b₀ i ∈ flagStep Ω b₀ i → π i e = t * π i (b₀ i) := by
    intro e t h
    have h1 : π i (e - t • b₀ i) = 0 := hker h
    simpa [sub_eq_zero] using h1

  have hbi : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [Flag.step_succ] at hbi
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hbi
  obtain ⟨u', rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hone : u' * π i (b₀ i) = 1 := by
    have h1 : π i (b i) = 1 := by simp [hπ]
    have h2 : π i z = 0 := hker hz
    rw [← hzw] at h1
    simpa [h2] using h1
  have hu' : u' ≠ 0 := left_ne_zero_of_mul_eq_one hone
  have hw0 : π i (b₀ i) ≠ 0 := right_ne_zero_of_mul_eq_one hone
  have hcls : b i - u' • b₀ i ∈ flagStep Ω b₀ i := by
    have : b i - u' • b₀ i = z := by rw [← hzw]; abel
    rw [this]; exact hz

  have hreg : ∀ e ∈ V p, π i e ∈ regAt ξ p := by
    intro e he
    rw [hfr.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hπ]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul s x _ hx =>
      have : π i (s • x) = (s : Ω) * π i x := (π i).map_smul (s : Ω) x
      rw [this]
      exact mul_mem s.2 hx

  have hgen : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {u'} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro s ⟨e, he, hs⟩
      have h1 := hkill e s hs
      refine Submodule.mem_span_singleton.2 ⟨⟨π i e, hreg e he⟩, ?_⟩
      show π i e * u' = s
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    · rintro _ rfl
      exact ⟨b i, by rw [hfr.2]; exact Submodule.subset_span ⟨i, rfl⟩, hcls⟩
  have hdeg : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    have := hD.2 p (Set.mem_univ p) c hc
    rw [this]
    rfl
  have hspan : Submodule.span (regAt ξ p) {u'} = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hgen, hdeg]
  have a1 : u' ∈ Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hspan]; exact Submodule.mem_span_singleton_self _
  have a2 : gen y a e₀ c ∈ Submodule.span (regAt ξ p) {u'} := by
    rw [hspan]; exact Submodule.mem_span_singleton_self _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 a2
  have hα' : (α : Ω) * gen y a e₀ c = u' := hα
  have hβ' : (β : Ω) * u' = gen y a e₀ c := hβ
  have hg0 : gen y a e₀ c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα'
    exact hu' hα'.symm
  have hκ : u' / gen y a e₀ c = α := by
    rw [← hα']; field_simp
  have hκi : (u' / gen y a e₀ c)⁻¹ = β := by
    rw [inv_div, ← hβ']; field_simp
  refine ⟨b, π, u' / gen y a e₀ c, hf, hfr, hm, hπ, hr, div_ne_zero hu' hg0, ?_, ?_, ?_⟩
  · rw [hκ]; exact α.2
  · rw [hκi]; exact β.2
  · intro e t _ hcl
    have h1 := hkill e t hcl
    have h2 : t = π i e * u' := by
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    rw [h2, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem actComm_aug_subst {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' R) :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetSubstP m φ) = jetAug := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  show MvPolynomial.aeval (fun _ => (0 : R)) (MvPolynomial.aeval (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) (MvPolynomial.X i)) = MvPolynomial.aeval (fun _ => (0 : R)) (MvPolynomial.X i)
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_zero']

theorem actComm_aug_X {R : Type} [CommRing R] {κ : Type} (m : ℕ) (q : κ) :
    (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0
  simp

theorem actComm_homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A]
    [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Fib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) :
    homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, fibPt_fst, fibPt_fst, Over.comp_left]
    rfl
  · rw [Over.comp_left, Category.assoc, fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem fibPt_map {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) (b : t.G ⟶ t.G) :
    fibPt t x y ≫ (Over.pullback x).map b = fibPt t x (y ≫ b) := by
  have h1 : ((Over.pullback x).map b).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ b.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback x).map b).left ≫ pullback.snd t.G.hom x = pullback.snd t.G.hom x :=
    pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, h1, ← Category.assoc, fibPt_fst, fibPt_fst, Over.comp_left]
  · rw [Over.comp_left, Category.assoc, h2, fibPt_snd, fibPt_snd]

end Fib

theorem substitution_action_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (m : ℕ) (a : 𝓞 E), (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2)).comp (sub1 Qs m) = (sub1 Qs m).comp (jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2)) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB Qs _ hQ m a
  set A := jetSubstP (S := k) m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2) with hA
  set B := jetSubstP (S := k) m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2) with hB
  have h1 : homAt (𝟙 (Sp k)) (A.comp (sub1 Qs m)) ≫ gB.x m =
      fibPt t x (g.x m) ≫ (Over.pullback x).map (t.act.act a) ≫ Q.q := by
    rw [← actComm_homAt_comp, Category.assoc, ← hQ m, ← Category.assoc, homAt_fibPt, ← g.chart.act m a,
      ← fibPt_map, Category.assoc]
  have h2 : homAt (𝟙 (Sp k)) ((sub1 Qs m).comp B) ≫ gB.x m =
      fibPt t x (g.x m) ≫ (Over.pullback x).map (t.act.act a) ≫ Q.q := by
    rw [← actComm_homAt_comp, Category.assoc, ← gB.chart.act m a, Q.act_q, ← Category.assoc, ← Category.assoc, ← hQ m]
  have haug : ∀ χ : Jet k (Fin 1 × Fin d') m →ₐ[k] Jet k (Fin 1 × Fin d) m,
      (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp χ = jetAug →
      ∀ q, (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0 := by
    intro χ h q
    rw [← AlgHom.comp_apply, h, actComm_aug_X]
  have a1 : (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp (A.comp (sub1 Qs m)) = jetAug := by
    rw [← AlgHom.comp_assoc, hA, actComm_aug_subst, sub1, actComm_aug_subst]
  have a2 : (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k).comp ((sub1 Qs m).comp B) = jetAug := by
    rw [← AlgHom.comp_assoc, sub1, actComm_aug_subst, hB, actComm_aug_subst]
  have hz : homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫
      (homAt (𝟙 (Sp k)) (A.comp (sub1 Qs m)) ≫ gB.x m) = 1 := by
    rw [← Category.assoc, actComm_homAt_comp, a1]
    exact gB.chart.zero m
  exact ((GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ hz).unique
    ⟨haug _ a1, rfl⟩ ⟨haug _ a2, h1.trans h2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap

open Formalism.MainNotions.ModuliIntegralCharts.H1

section Jets

variable {k : Type} [CommRing k]

theorem exists_jetMap {κ κ' : Type} {m : ℕ} (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (h : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ'), χ = jetMap φ hφ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.X q)))
  have hc : ∀ q, MvPolynomial.constantCoeff (P q) = 0 := fun q => by
    have e : (jetAug : Jet k κ' m →ₐ[k] k) (Ideal.Quotient.mk _ (P q)) = 0 := by rw [hP]; exact h q
    have e' : (MvPolynomial.aeval (fun _ : κ' => (0 : k))) (P q) = 0 := e
    rwa [MvPolynomial.aeval_zero'] at e'
  have hm : ∀ q, P q ∈ orig k κ' := fun q => by
    have := sub_const_mem_orig (P q)
    rwa [hc q, map_zero, sub_zero] at this
  refine ⟨P, hm, GermD.jet_hom_ext fun q => ?_⟩
  rw [GermD.jetMap_mk, MvPolynomial.aeval_X, hP]

end Jets

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (by simp)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_fst, fibPt_fst]
    rfl
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem one_left_fst {T : Over (Sp k)} :
    (1 : T ⟶ GF t x).left ≫ pullback.fst t.G.hom x = T.hom ≫ x ≫ η[t.G].left := by
  rw [Hom.one_def, Over.comp_left, Category.assoc]
  have e : η[(Over.pullback x).obj t.G].left ≫ pullback.fst t.G.hom x = x ≫ η[t.G].left := by
    rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
      ← pullback.condition_assoc]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  erw [e]
  rfl

theorem fibPt_one {A : Type} [CommRing A] [Algebra k A] : fibPt t x (1 : overAt x A ⟶ t.G) = 1 := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · erw [fibPt_fst, one_left_fst]
    rw [Hom.one_def, Over.comp_left]
    simp
  · erw [fibPt_snd]
    have := Over.w (1 : overAt (𝟙 (Sp k)) A ⟶ GF t x)
    simpa using this.symm

end Fibre

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {x : Sp k ⟶ X}

theorem q_one (Q : AbQuot t x) {T : Over (Sp k)} : (1 : T ⟶ GF t x) ≫ Q.q = 1 := by
  have := Q.q_hom
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

theorem chart_trunc {S : Type} [CommRing S] {Y : Scheme.{0}} {G : Over Y} (x₀ : Sp S ⟶ Y) {d e : ℕ}
    (gx : ∀ m, jOG x₀ e m 1 ⟶ G)
    (htr : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) ≫ gx (m + 1) = gx m)
    (y : ∀ m, overAt x₀ (Jet S (Fin 1 × Fin d) m) ⟶ G)
    (hy : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ y (m + 1) = y m)
    (χ : ∀ m, Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m)
    (hz : ∀ m q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (χ m (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0)
    (hχ : ∀ m, y m = homAt x₀ (χ m) ≫ gx m)
    (hu : ∀ m (ψ : Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m),
      (∀ q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) →
        y m = homAt x₀ ψ ≫ gx m → ψ = χ m) (m : ℕ) (q : Fin 1 × Fin e) :
    (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)
      (χ (m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X q))) = χ m (Ideal.Quotient.mk _ (MvPolynomial.X q)) := by
  obtain ⟨φ, hφ, e₁⟩ := exists_jetMap (χ (m + 1)) (hz (m + 1))
  have hcomm : (jetMap (m := m) φ hφ).comp
      (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) =
      (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m).comp (χ (m + 1)) := by
    rw [e₁]
    exact GermD.jet_hom_ext fun i => rfl
  have hψ : jetMap (m := m) φ hφ = χ m := by
    refine hu m _ (fun q => ?_) ?_
    · have h := hz (m + 1) q
      rw [e₁] at h
      exact h
    · rw [← hy m, hχ (m + 1), ← htr m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp, hcomm]
  rw [← hψ]
  exact (AlgHom.congr_fun hcomm _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB
  have hy₀ : ∀ m, homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ (fibPt t x (g.x m) ≫ Q.q) = 1 := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.zero m, fibPt_one, q_one]
  have hy₁ : ∀ m, homAt (𝟙 (Sp k)) (jetTrunc : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m) ≫
      (fibPt t x (g.x (m + 1)) ≫ Q.q) = fibPt t x (g.x m) ≫ Q.q := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.trunc m]
  choose χ hχ hu using fun m =>
    (GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ (hy₀ m)
  have hc := chart_trunc (𝟙 (Sp k)) gB.x gB.chart.trunc (fun m => fibPt t x (g.x m) ≫ Q.q) hy₁ χ
    (fun m => (hχ m).1) (fun m => (hχ m).2) (fun m ψ h₁ h₂ => hu m ψ ⟨h₁, h₂⟩)
  choose Qs hQs using fun i : Fin d' => GaugeR.exists_ps_of_compat
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => hc m _)
  have hconst : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0 := fun i => by
    rw [← GaugeR.jetAug_psJet 0 (Qs i), hQs i 0]
    exact (hχ 0).1 _
  refine ⟨Qs, hconst, fun m => ?_⟩
  have he : sub1 Qs m = χ m := by
    refine GermD.jet_hom_ext fun q => ?_
    obtain ⟨a, i⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have h0 : MvPolynomial.constantCoeff (psTrunc m (Qs i)) = 0 := by
      rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp)]
      exact hconst i
    rw [← hQs i m, sub1, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X, h0, map_zero, sub_zero]
    rfl
  rw [he]
  exact (hχ m).2

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.line_bundle_pullback_generator : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.theorem_of_cube_section_value : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {T : Over S} (x a : T ⟶ G) (m : ℕ), x ^ m = 1 → ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U), v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen <;> assumption)
end
