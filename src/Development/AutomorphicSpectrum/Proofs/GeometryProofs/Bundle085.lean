module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle077
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem fullLevel_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) :=
  PositivityTheory.HtPt.Mg.level_props

end GlobalTheory.CompanionTheory.Ar.XR
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.is_comb_identity_matrix : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) → ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | exact GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.smooth_generic_fibre_of_snc : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y e bd → SmoothGenericFibreM y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {Em : Type}
  [AddCommGroup Em] [Module R Em]

theorem isComb_pt_iff (M : LieModel G x Em) {n : ℕ} (b : Fin n → Em) (cf : Fin n → R) (w : epsAt x ⟶ G) :
    IsComb cf (fun i => M.pt (b i)) w ↔ w = M.pt (∑ i, cf i • b i) := by
  have hsum : M.pt (∑ i, cf i • b i) = (List.ofFn fun i => M.pt (cf i • b i)).prod :=
    GlobalTheory.CompanionTheory.Ar.CombEig.pt_sum M fun i => cf i • b i
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hue : u = fun i => M.pt (cf i • b i) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu i, M.smul])
    rw [hsum, hue]
  · rintro rfl
    exact ⟨fun i => M.pt (cf i • b i), fun i => M.smul _ _, hsum⟩

theorem isEigVec_pt_iff {Oe : Type} [CommRing Oe] (M : LieModel G x Em) (act : OAct Oe G)
    {ρ : Oe →+* Module.End R Em} (τ : Oe →+* R) (hρ : M.IsActOf act.act ρ) (e : Em) :
    IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  have hmem : e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [hmem]
  constructor
  · intro h a
    exact M.inj (Over.OverMorphism.ext (by rw [hρ a e, M.smul]; exact h.2 a))
  · intro h
    exact ⟨M.tan e, fun a => by rw [← hρ a e, h a, M.smul]⟩

theorem isEigFrame_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  intro S R _ G _ _ x Em _ _ M Oe _ act ρ τ n b hρ
  have eig := isEigVec_pt_iff M act τ hρ
  have key := isComb_pt_iff M b
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).1 (h1 i), fun e he => ?_⟩
    obtain ⟨c, hc, hu⟩ := h2 (M.pt e) ((eig e).2 he)
    exact ⟨c, M.inj ((key c _).1 hc), fun c' hc' => hu c' ((key c' _).2 (congrArg M.pt hc'))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).2 (h1 i), fun w hw => ?_⟩
    obtain ⟨e, rfl⟩ := M.onto w hw.1
    obtain ⟨c, hc, hu⟩ := h2 e ((eig e).1 hw)
    exact ⟨c, (key c _).2 (congrArg M.pt hc), fun c' hc' => hu c' (M.inj ((key c' _).1 hc'))⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.eigenvector_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | exact GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.is_comb_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | exact GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | (intros; apply GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.is_comb_matrix_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | exact GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  first | exact @PositivityTheory.Xgf.hodge_gram_linear_combination | exact PositivityTheory.Xgf.hodge_gram_linear_combination
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Bridge

theorem comb_eig_frame : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ :=
  @PositivityTheory.Xgf.lie_model_eigenvectors_action

end GlobalTheory.CompanionTheory.Ar.Fl.Bridge
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_ext {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (τ : 𝓞 E →+* K) :
    ∃ ψ : E →+* K, ψ.comp (algebraMap (𝓞 E) E) = τ := by
  have hker : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [Ideal.under_def, RingHom.comap_ker, RingHom.ker_eq_bot_iff_eq_zero]
    intro n hn
    simpa using hn
  have hinj : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot τ).mpr hker
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

theorem charZero_of_coeff {F : IntermediateField ℚ ℂ} {k : Type} [Field k] (φ : F →+* k) : CharZero k :=
  (RingHom.charZero_iff (φ.comp (algebraMap ℚ F)).injective).mp inferInstance

theorem exists_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {k : Type} [Field k] [IsAlgClosed k] (φ : c.F →+* k) (ψ : E →+* k) :
    ∃ τ₁ : E →+* ℂ, φ.comp (τ₁.codRestrict c.F (c.conj τ₁)) = ψ := by
  haveI : CharZero k := charZero_of_coeff φ
  let g : (E →+* ℂ) → (E →+* k) := fun τ => φ.comp (τ.codRestrict c.F (c.conj τ))
  have hg : Function.Injective g := by
    intro τ τ' h
    ext a
    have h1 := RingHom.congr_fun h a
    simp only [g, RingHom.comp_apply] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* k) := by
    rw [NumberField.Embeddings.card, NumberField.Embeddings.card]
  obtain ⟨τ₁, hτ₁⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2 ψ
  exact ⟨τ₁, hτ₁⟩

theorem exists_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (ρ₀ : c.F), (ρ₀ : ℂ) = H.rt0 → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (τ : 𝓞 E →+* k),
    (τ H.rt = φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inl t)) = τ) ∧
    (τ H.rt ≠ φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inr t)) = τ) := by
  intro E _ _ _ H l c ρ₀ hρ₀ k _ _ φ τ
  haveI : CharZero k := charZero_of_coeff φ
  obtain ⟨ψ, hψ⟩ := exists_ext τ
  obtain ⟨τ₁, hτ₁⟩ := exists_factor c φ ψ
  have key : ∀ a : 𝓞 E, φ ⟨τ₁ (a : E), c.conj τ₁ (a : E)⟩ = τ a := by
    intro a
    rw [← hψ, ← hτ₁]
    rfl
  have hrt : τ₁ (H.rt : E) = H.rt0 ↔ τ H.rt = φ ρ₀ := by
    constructor
    · intro h
      rw [← key]
      congr 1
      exact Subtype.ext (h.trans hρ₀.symm)
    · intro h
      rw [← key] at h
      rw [← hρ₀]
      exact congrArg Subtype.val (φ.injective h)
  refine ⟨fun h => ⟨⟨τ₁, hrt.mpr h⟩, RingHom.ext fun a => key a⟩, fun h => ?_⟩
  have hne : τ₁ (H.rt : E) ≠ H.rt0 := fun h' => h (hrt.mp h')
  have hsqE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ₁ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsqE, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  have hneg : τ₁ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exfalso
      rw [h4] at h1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) (-H.rt0) = H.rt0 := by
    apply Complex.ext <;> simp [hre]
  refine ⟨⟨τ₁.comp (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, ?_⟩
  · show τ₁ (NumberField.IsCMField.complexConj E (H.rt : E)) = H.rt0
    rw [NumberField.IsCMField.complexEmbedding_complexConj, hneg, hconj]
  · refine RingHom.ext fun a => ?_
    rw [← key a, RingHom.comp_apply]
    refine congrArg φ (Subtype.ext ?_)
    show τ₁ (NumberField.IsCMField.complexConj E ((H.bar a : 𝓞 E) : E)) = τ₁ (a : E)
    rw [H.bar_eq, NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.LabelCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem labels_all_once : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H)
    (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧
      Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c
  classical
  have hre : H.rt0.re = 0 := by
    have h : (H.rt0 * H.rt0).re = (-(H.d : ℂ)).re := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h
    have h' : (H.rt0 * H.rt0).im = (-(H.d : ℂ)).im := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h'
    have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by nlinarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact mul_self_eq_zero.1 h3
    · nlinarith [mul_self_nonneg H.rt0.re]
  have hconj0 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h
    exact H.d_prime.ne_zero h
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    apply hne
    have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · exact h3
  have hsq : ∀ τ : E →+* ℂ, (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    have e1 := congrArg (fun x : 𝓞 E => τ (algebraMap (𝓞 E) E x)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at e1
    rw [H.sqrt_neg_disc_sq]
    exact e1
  have hpm : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 :=
    fun τ => sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ)
  have hcc : ∀ τ : E →+* ℂ, τ (IsCMField.complexConj E (H.rt : E)) = -τ (H.rt : E) := by
    intro τ
    rw [IsCMField.complexEmbedding_complexConj]
    rcases hpm τ with h | h
    · rw [h, hconj0]
    · rw [h, map_neg, hconj0]
  refine ⟨?_, ?_⟩
  · have k1 : ∀ (τ : CMType H) (x : 𝓞 E), ((labelEmb c (Sum.inl τ) x : ℂ)) = τ.1 (x : E) :=
      fun _ _ => rfl
    have k2 : ∀ (τ : CMType H) (x : 𝓞 E),
        ((labelEmb c (Sum.inr τ) x : ℂ)) = τ.1 ((H.bar x : 𝓞 E) : E) := fun _ _ => rfl
    have ext' : ∀ τ τ' : E →+* ℂ, (∀ x : 𝓞 E, τ (x : E) = τ' (x : E)) → τ = τ' := by
      intro τ τ' h
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
    rintro (τ | τ) (τ' | τ') h
    · refine congrArg Sum.inl (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h x)
      rwa [k1, k1] at e
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k1, k2, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e.symm
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k2, k1, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e
    · refine congrArg Sum.inr (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h (H.bar.symm x))
      rwa [k2, k2, RingEquiv.apply_symm_apply] at e
  · let e : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq, τ.2, hconj0]
            exact hneg⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq]
            rcases hpm τ.1 with h | h
            · exact absurd h τ.2
            · rw [h, map_neg, hconj0, neg_neg]⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq])
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq]) }
    have hc : Nat.card (CMType H ⊕ CMType H) = Nat.card (E →+* ℂ) :=
      Nat.card_congr ((Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.sumCompl _))
    rw [hc, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem exists_lift_of_mem_range {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (x : Sp ℂ ⟶ X)
    (p : Sp ℂ) (hp : x p ∈ Set.range i) : ∃ t : Sp ℂ ⟶ Z, t ≫ i = x := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hs : Surjective (pullback.snd i x) :=
    ⟨fun q => ⟨w, by rw [hw]; exact Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i x)
  exact ⟨inv (pullback.snd i x) ≫ pullback.fst i x, by simp [pullback.condition]⟩

theorem one_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem mem_per_of_frequently : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  intro R _ G _ _ g n M B ψ e hsep hψ b₀ hb₀ s hs hfr
  haveI := hsep
  by_contra hne
  have hid : η[G].left ≫ G.hom = 𝟙 _ := Over.w _
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp _ G.hom
  let V : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, by
    letI := hη
    exact η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV₀ : ⊤ ≤ (e.ex b₀ (s b₀)).left ⁻¹ᵁ V := by
    intro p _
    show (e.ex b₀ (s b₀)).left p ∉ Set.range η[G].left
    intro hp
    obtain ⟨t, ht⟩ := exists_lift_of_mem_range η[G].left (e.ex b₀ (s b₀)).left p hp
    apply hne
    show e.ex b₀ (s b₀) = 1
    apply Over.OverMorphism.ext
    have h1 : t = spMap (ψ b₀) := by
      have h2 := Over.w (e.ex b₀ (s b₀))
      have h4 : (t ≫ η[G].left) ≫ G.hom = spMap (ψ b₀) := by rw [ht]; exact h2
      rw [Category.assoc, hid] at h4
      exact h4
    rw [one_left_eq, ← ht, h1]
    rfl
  have hopen := (e.hol V 0).1
  have hmem : (b₀, s b₀) ∈ {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ V} :=
    ⟨⟨hb₀, trivial⟩, hV₀⟩
  have hcont : ContinuousAt (fun b => (b, s b)) b₀ := continuousAt_id.prodMk hs
  have hev := hcont.eventually (hopen.mem_nhds hmem)
  obtain ⟨b, ⟨-, hper⟩, -, hb⟩ := (hfr.and_eventually hev).exists
  have hper' : e.ex b (s b) = 1 := hper
  have hb' : ⊤ ≤ (e.ex b (s b)).left ⁻¹ᵁ V := hb
  rw [hper'] at hb'
  let p : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have hp : (1 : Over.mk (spMap (ψ b)) ⟶ G).left p ∉ Set.range η[G].left := hb' (show p ∈ ⊤ from trivial)
  apply hp
  rw [one_left_eq]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
