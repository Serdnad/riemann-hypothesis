module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle056
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle012
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle014
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieVB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x hT c p hp a).1 ha

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

end Chart

section Bundle

variable {κ : Type} {x : κ → Ω} {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

end Bundle

end GlobalTheory.CompanionTheory.Ar.TieVB

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.order_valuation_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | exact GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.complex_points_dense_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | exact GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.exists_complex_point_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_ptOver_ne | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_ptOver_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_ptOver_ne <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.unit_section_avoid_prime : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_vector_bundle_of_smooth : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → M.lat.IsVB g ⊤ ∧ M.omLat.IsVB g ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_isVB | exact GlobalTheory.CompanionTheory.Ar.lieLat_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_isVB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_tate_weil_endomorphism : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | exact GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | (intros; apply GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lineLat_isVBOn_gen_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) :=
  @PositivityTheory.Xgn.line_lattice_vector_bundle

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lattice_generator_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_spread

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.complex_conjugation_herm_compat : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], (∀ (P : Ideal (MRing ι)) z, conjPt z ∈ mcPts P ↔ z ∈ mcPts P) ∧ (∀ (z : (Σ k, ι k) → ℂ) f, evC (conjPt z) f = starRingEnd ℂ (evC z f)) ∧ (∀ A : HermLine ι, IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ (∀ (A : HermLine ι) s z, logNorm (conjLine A) s z = logNorm A s (conjPt z)) ∧ (∀ A B : HermLine ι, conjLine (A.tensor B) = (conjLine A).tensor (conjLine B)) ∧ ∀ A : HermLine ι, conjLine (conjLine A) = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.conj_basic | exact GlobalTheory.CompanionTheory.Ar.Cmp.conj_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.conj_basic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem curveIn_isDeg_unique_of_isCptGen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' :=
  @PositivityTheory.HtPt.Ch.isdeg_unique

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem fullTorsion_of_dominates : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ n hd hp hf k _ i' g hg
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  have e : (spMap i' ≫ ξ') ≫ f = spMap (i'.comp i) ≫ ξ := by
    rw [Category.assoc, hd', ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : (Over.mk (spMap i' ≫ ξ') ⟶ G') →* (Over.mk ((spMap i' ≫ ξ') ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
  have ha : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (u : Over.mk a ⟶ G), u ^ n = 1 →
      ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
    intro a b h u hu
    subst h
    exact ⟨u, rfl, hu⟩
  obtain ⟨u, hl, hu⟩ := tr e (ρ g) ha
  obtain ⟨x, hx⟩ := hf k (i'.comp i) u hu
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  have hw : (spMap i ≫ x.left) ≫ G.hom = ξ' ≫ f := by
    rw [Category.assoc, hxw, hd']
  have hs : spMap (i'.comp i) = spMap i' ≫ spMap i := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (hp.1.lift (spMap i ≫ x.left) ξ' hw) (hp.1.lift_snd _ _ _), ?_⟩
  apply hp.1.hom_ext
  · have h1 : g.left ≫ φ = spMap (i'.comp i) ≫ x.left := by
      rw [← hx, hl]
      rfl
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [h1, hs, Category.assoc]
  · have h2 : g.left ≫ G'.hom = spMap i' ≫ ξ' := by simpa using Over.w g
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    exact h2

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end
