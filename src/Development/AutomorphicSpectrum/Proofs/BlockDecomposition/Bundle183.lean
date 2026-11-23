module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle143
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle172
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamFiniteAndFiltrationBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DerivExt

theorem exists_derivation_ext {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : f.comp (algebraMap K A) = algebraMap K B) (M : Submonoid A)
    (hloc : letI := f.toAlgebra; IsLocalization M B) (D : Derivation K A A) :
    ∃ p : Derivation K B B, ∀ x, p (f x) = f (D x) := by
  letI := f.toAlgebra
  let φ : A →+* TrivSqZeroExt B B :=
    { toFun := fun x => (f x, f (D x))
      map_one' := by
        ext <;> simp
      map_zero' := by
        ext <;> simp
      map_add' := fun x y => by
        ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [Derivation.leibniz]
          ring }
  have hu : ∀ y : M, IsUnit (φ y) := fun y => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsLocalization.map_units B y
  let ψ : B →+* TrivSqZeroExt B B := IsLocalization.lift hu
  have hψ : ∀ x, ψ (f x) = φ x := fun x => IsLocalization.lift_eq hu x
  have hfst : ∀ b, (ψ b).fst = b := by
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp ψ = RingHom.id B :=
      IsLocalization.ringHom_ext M (RingHom.ext fun x => by
        change (ψ (f x)).fst = f x
        rw [hψ]; rfl)
    exact fun b => congrArg (· b) (congrArg DFunLike.coe this)
  have hmul : ∀ b c, (ψ (b * c)).snd = b * (ψ c).snd + c * (ψ b).snd := fun b c => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul]
    simp [hfst, mul_comm]
  have hadd : ∀ b c, (ψ (b + c)).snd = (ψ b).snd + (ψ c).snd := fun b c => by
    rw [map_add (f := _), TrivSqZeroExt.snd_add]
  have hsm : ∀ (k : K) b, (ψ (k • b)).snd = k • (ψ b).snd := fun k b => by
    have e : algebraMap K B k = f (algebraMap K A k) := (congrArg (· k) (congrArg DFunLike.coe hf)).symm
    rw [Algebra.smul_def, Algebra.smul_def, hmul, e, hψ]
    have : (φ (algebraMap K A k)).snd = 0 := by
      change f (D _) = 0
      rw [Derivation.map_algebraMap, map_zero]
    rw [this, mul_zero, add_zero]
  let L : B →ₗ[K] B :=
    { toFun := fun b => (ψ b).snd
      map_add' := hadd
      map_smul' := hsm }
  refine ⟨Derivation.mk' L fun b c => ?_, fun x => ?_⟩
  · change (ψ (b * c)).snd = b • (ψ c).snd + c • (ψ b).snd
    rw [hmul]; rfl
  · change (ψ (f x)).snd = _
    rw [hψ]; rfl

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {V : X.Opens}, IsAffineOpen V → ∀ (a : Γ(X, V)),
    letI := (strV q V).toAlgebra
    letI := (strV q (X.basicOpen a)).toAlgebra
    ∀ {d : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), ∃ p : Fin d → Derivation K Γ(X, X.basicOpen a) Γ(X, X.basicOpen a),
      ∀ k x, p k (rs (X.basicOpen_le a) x) = rs (X.basicOpen_le a) (D k x) := by
  intro K _ X q V hV a
  letI := (strV q V).toAlgebra
  letI := (strV q (X.basicOpen a)).toAlgebra
  intro d D
  have hloc : letI := (rs (X.basicOpen_le a)).toAlgebra; IsLocalization (Submonoid.powers a) Γ(X, X.basicOpen a) := by
    letI := (rs (X.basicOpen_le a)).toAlgebra
    exact hV.isLocalization_basicOpen a
  have hf : (rs (X.basicOpen_le a)).comp (algebraMap K Γ(X, V)) = algebraMap K Γ(X, X.basicOpen a) :=
    GlobalTheory.CompanionTheory.CoordRes.rs_comp_strV q _
  choose p hp using fun k => exists_derivation_ext _ hf _ hloc (D k)
  exact ⟨p, hp⟩

end GlobalTheory.CompanionTheory.ConeLocal.DerivExt
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.jacobian_span_le_subalgebra : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  first | exact @GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | exact GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | (intros; apply GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem main : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  intro R _ X D N i h
  obtain ⟨-, s, hs, -⟩ := h
  rw [eq_top_iff]
  intro x _
  obtain ⟨j, hj⟩ := GlobalTheory.ProjSpace.exists_mem_chart R N (i x)
  haveI : IsOpenImmersion (chart R N j) := by
    unfold chart
    infer_instance
  have hmem : (pullback.fst i (chart R N j)).opensRange ∈ 𝒱D D :=
    ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, by
      rw [Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]⟩
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨_, hmem, ?_⟩
  have e : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  have hr : i x ∈ ((chart R N j).opensRange : Set _) := by
    rw [e]
    exact hj
  rw [Scheme.Hom.coe_opensRange] at hr
  show x ∈ ((pullback.fst i (chart R N j)).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]
  exact hr

end GlobalTheory.CompanionTheory.ConeCover
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeChart

attribute [local instance] MvPolynomial.gradedAlgebra

instance isOpenImmersion_chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    IsOpenImmersion (chart R N j) := by
  unfold chart
  infer_instance

theorem opensRange_fst {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (j : Fin (N + 1)) :
    (pullback.fst i (chart R N j)).opensRange = i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j := by
  have hr : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  rw [← hr]
  ext x
  change x ∈ Set.range (pullback.fst i (chart R N j)) ↔ i x ∈ Set.range (chart R N j)
  rw [Scheme.Pullback.range_fst]
  rfl

theorem preimage_chart_mem {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (h : IsTautologicalLineAt D N i) (j : Fin (N + 1)) :
    i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j ∈ 𝒱D D := by
  obtain ⟨_, s, hs, _⟩ := h
  rw [← opensRange_fst]
  refine ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, ?_⟩
  rw [Category.assoc, hs, Iso.inv_comp_eq]
  exact (Scheme.Hom.isoOpensRange_hom_ι _).symm

end GlobalTheory.CompanionTheory.ConeChart
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeZcoc

theorem plogK_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (s : ℕ)
    {x : B} (hx : x ∈ J) : f (plogK δ s x) = plogK δ' s (f x) := by
  unfold plogK

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, ← hf.2 x hx]

theorem units_cancel {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * c⁻¹) * (c * d * e⁻¹) = (b * d * f⁻¹) * (a * f * e⁻¹) := by
  have h1 : (a * b * c⁻¹) * (c * d * e⁻¹) = a * b * d * e⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : (b * d * f⁻¹) * (a * f * e⁻¹) = (a * b * d) * e⁻¹ * (f⁻¹ * f) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2, inv_mul_cancel, mul_one]

theorem plogK_four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (hs : pdP δ s = ⊥)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J)
    (hd : d - 1 ∈ J) (h : a * b = c * d) :
    plogK δ s (a - 1) + plogK δ s (b - 1) = plogK δ s (c - 1) + plogK δ s (d - 1) := by
  rw [← GlobalTheory.T.truncated_log_multiplicative δ s hs hu ha hb, ← GlobalTheory.T.truncated_log_multiplicative δ s hs hu hc hd]
  simp only [add_sub_cancel]
  rw [h]

theorem add_eq {B : Type} [CommRing B] {a c d b a' c' d' b' : B} (h₁ : a = a') (h₂ : c = c') (h₃ : d = d')
    (h₄ : b = b') (h : a' + c' = d' + b') : a + c = d + b := by
  rw [h₁, h₂, h₃, h₄, h]

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def rr (Λ : CLiftK g D) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c) : (g.obj c).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem r_eq (Λ : CLiftK g D) (σ : ComposableArrows C 2) :
    Λ.r σ = rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) := rfl

theorem rr_coboundary (Λ : CLiftK g D) {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃)
    (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f₀₃ : c₀ ⟶ c₃) (h₀₂ : f₀₂ = f₀₁ ≫ f₁₂) (h₁₃ : f₁₃ = f₁₂ ≫ f₂₃) :
    Units.map (g.map f₂₃).φ.toMonoidHom (rr Λ f₀₁ f₁₂ f₀₂) * rr Λ f₀₂ f₂₃ f₀₃ =
      rr Λ f₁₂ f₂₃ f₁₃ * rr Λ f₀₁ f₁₃ f₀₃ := by
  subst h₀₂ h₁₃
  have e : Units.map (g.map (f₁₂ ≫ f₂₃)).φ.toMonoidHom (Λ.w f₀₁) =
      Units.map (g.map f₂₃).φ.toMonoidHom (Units.map (g.map f₁₂).φ.toMonoidHom (Λ.w f₀₁)) := by
    rw [g.map_comp]; rfl
  unfold rr
  rw [e, map_mul, map_mul, map_inv]
  exact units_cancel _ _ _ _ _ _

theorem map_zK (Λ : CLiftK g D) (s : ℕ) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    (show (g.obj c).B from ((g ⋙ O (smFun X q)).map ρ).hom (zK Λ s σ)) =
      plogK (g.obj c).δ s (((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1) := by
  change (g.map ρ).φ (plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) = _
  rw [plogK_map (g.map ρ).dp s (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ), map_sub, map_one]
  rfl

theorem mem_J (Λ : CLiftK g D) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    ((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1 ∈ (g.obj c).J := by
  have := (g.map ρ).hle (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ)
  rw [Ideal.mem_comap, map_sub, map_one] at this
  exact this

theorem map_id_unit {c : C} (ρ : c ⟶ c) (h : ρ = 𝟙 c) (u : (g.obj c).Bˣ) :
    Units.map (g.map ρ).φ.toMonoidHom u = u := by
  subst h
  rw [g.map_id]
  ext; rfl

theorem nat_isUnit (T : Thick (smFun X q)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : T.B) := by
  have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn).isUnit
  have := h.map T.i
  rwa [map_natCast] at this

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  intro K _ _ X q C _ g D Λ s hs
  funext τ
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (toLast i τ)).hom (zK Λ s (face i τ)) = 0
  rw [Fin.sum_univ_four]
  have h0 := map_zK Λ s (face 0 τ) (toLast 0 τ)
  have h1 := map_zK Λ s (face 1 τ) (toLast 1 τ)
  have h2 := map_zK Λ s (face 2 τ) (toLast 2 τ)
  have h3 := map_zK Λ s (face 3 τ) (toLast 3 τ)
  have m0 := mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := plogK_four (g.obj (τ.obj (Fin.last 3))).δ s (hs _) (nat_isUnit (g.obj (τ.obj (Fin.last 3)))) m3 m1 m0 m2 hval
  have fin : ∀ a b c d : (g ⋙ O (smFun X q)).obj (τ.obj (Fin.last 3)), a + c = d + b →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro a b c d h
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    rw [e0, e1, e2, e3]
    have : (-1 : ℤ) ^ 3 = -1 := by norm_num
    rw [this, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul, neg_one_smul]
    calc a + -b + c + -d = (a + c) - (d + b) := by abel
      _ = 0 := by rw [h, sub_self]
  refine fin _ _ _ _ ?_
  exact add_eq (B := (g.obj (τ.obj (Fin.last 3))).B) h0 h2 h3 h1 p.symm

end GlobalTheory.CompanionTheory.ConeZcoc
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cone_cocycle_class_independent : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → ∀ (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0), (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcls.main | exact GlobalTheory.CompanionTheory.ConeZcls.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcls.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedTrans

section
variable {O A R₁ R₂ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂]
  {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
  {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n s : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tr_dp (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (n : ℕ) :
    IsDPMorphism (redδ T h (n + 1)) (redδ T h n) (lnMap (RingHom.id T.B) l n.le_succ) := by
  have key : ∀ y : T.B, lnMap (RingHom.id T.B) l n.le_succ (Ideal.Quotient.mk (lnT T l (n + 1)) y) =
      Ideal.Quotient.mk (lnT T l n) y := fun y => by
    simp only [lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [Ideal.mem_comap, key]
    exact Ideal.mem_map_of_mem _ hy
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [key]
    simp only [redδ]
    rw [DividedPowers.Quotient.dpow_apply _ _ hy, DividedPowers.Quotient.dpow_apply _ _ hy, key]

variable (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {σ' : R₁ →+* R₂}
  (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')

theorem tr_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (r : R₁) :
    lnMap (RingHom.id T.B) l n.le_succ (iBar T l (n + 1) (d₁.ρ r)) = iBar T l n (d₂.ρ (σ' r)) := by
  rw [hρ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [← ha]
  simp only [iBar, lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]

def eta (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) : redObj T d₁ h ⟶ m.obj (redObj T d₂ h) :=
  mkH (lnMap (RingHom.id T.B) l n.le_succ) (tr_comm d₁ d₂ hρ T) (tr_dp T h n)
    (Ideal.map_le_iff_le_comap.1 (tr_dp T h n).1) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        refine Eq.trans ?_ ((m.obj (redObj T d₂ h)).w r).symm
        exact congrArg (Ideal.Quotient.mk _) (tr_comm d₁ d₂ hρ T r)
      · refine Eq.trans ?_ (hpt _ _).symm
        change Spec.map _ ≫ Spec.map _ ≫ pt T = Spec.map _ ≫ pt T
        rw [← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end

theorem red_trans : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := by
  intro O A R₁ R₂ Λ _ _ _ _ _ _ I γ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X q s 𝒱 σ' m c₁ c₂ lam hc₁ hc₂ h₀ hpt hρ r j x
  rw [CrystallineSemistableComparison.pull_pull lam, trM, CrystallineSemistableComparison.pull_pull lam]
  symm
  refine CrystallineSemistableComparison.cr_pull_eq (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R₁ J₁ δ₁ l) (ht := rfl) (κ := κ₁) _ _ ?η ?nat ?cmp j x
  case η => exact fun T => eta d₁ d₂ m hpt hρ T.obj T.property.1
  case nat =>
    intro T T' f y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl
  case cmp =>
    intro T y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl

end GlobalTheory.CompanionTheory.RedTrans
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.hodge_filtration_vanishes_above_dimension : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | exact GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | (intros; apply GlobalTheory.CompanionTheory.FilTop.fil_top_vanish <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.de_rham_finite_and_filtration_bounded : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → KH.GrCechFin → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] (j : ℕ),
    FiniteDimensional K (HdR q j) ∧ ∀ x ∈ FilR q j (j + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.main | exact GlobalTheory.CompanionTheory.KFin.main | (intros; apply GlobalTheory.CompanionTheory.KFin.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem coord_near : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] {V' : X.Opens}, IsAffineOpen V' → ∀ x : X, x ∈ V' →
    ∃ (f : Γ(X, V')) (e : ℕ) (c : Coord q (X.basicOpen f) e), x ∈ X.basicOpen f := by
  intro K _ X q _ V' hV x hx
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V' le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
  obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
    RingHom.isStandardSmooth_respectsIso q hV h hx
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨f, n, (GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he).some, hf⟩

end GlobalTheory.CompanionTheory.ConeLocal
end
