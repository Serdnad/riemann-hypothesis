module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.BetaFun
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089

@[expose] public section

section

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.SubEig

section Generic

variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]

def cyc (ρ : Representation ℂ G U) (u : U) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g u)
  apply_mem_toSubmodule g v hv := by
    have hle : Submodule.span ℂ (Set.range fun g : G => ρ g u) ≤
        (Submodule.span ℂ (Set.range fun g : G => ρ g u)).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact hle hv

theorem mem_cyc (ρ : Representation ℂ G U) (u : U) : u ∈ (cyc ρ u).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem exists_max_avoid (ρ : Representation ℂ G U) {u : U} (hu : u ≠ 0) :
    ∃ T : Subrepresentation ρ, u ∉ T.toSubmodule ∧
      ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T := by
  have hbot : (⊥ : Subrepresentation ρ) ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule} := by
    show u ∉ (⊥ : Submodule ℂ U)
    simpa using hu
  have hz : ∀ c ⊆ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rcases hchain.total ha hb with h | h
      · exact ⟨_, ⟨b, hb, rfl⟩, h, le_rfl⟩
      · exact ⟨_, ⟨a, ha, rfl⟩, le_rfl, h⟩
    have hmem : ∀ x, x ∈ sSup (Subrepresentation.toSubmodule '' c) ↔
        ∃ a ∈ c, x ∈ Subrepresentation.toSubmodule a := by
      intro x
      rw [Submodule.mem_sSup_of_directed hne hdir]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩
        exact ⟨a, ha, hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨_, ⟨a, ha, rfl⟩, hx⟩
    refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), ?_⟩, ?_, ?_⟩
    · intro g v hv
      obtain ⟨a, ha, hx⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a, ha, a.apply_mem_toSubmodule g hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := (hmem u).1 h
      exact hc ha hx
    · intro z hz x hx
      exact (hmem x).2 ⟨z, hz, hx⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ {T : Subrepresentation ρ | u ∉ T.toSubmodule} hz ⊥ hbot
  exact ⟨T, hT.prop, fun T' hle hu' => le_antisymm (hT.le_of_ge hu' hle) hle⟩

theorem cyc_gen (ρ : Representation ℂ G U) (u : U)
    (R : Subrepresentation (cyc ρ u).toRepresentation)
    (hR : (⟨u, mem_cyc ρ u⟩ : (cyc ρ u).toSubmodule) ∈ R.toSubmodule) : R = ⊤ := by
  have hle : (cyc ρ u).toSubmodule ≤ R.toSubmodule.map (cyc ρ u).toSubmodule.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨_, R.apply_mem_toSubmodule g hR, rfl⟩
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem quot_irred (ρ : Representation ℂ G U) (T : Subrepresentation ρ) {u : U}
    (hu : u ∉ T.toSubmodule)
    (hmax : ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T)
    (hgen : ∀ R : Subrepresentation ρ, u ∈ R.toSubmodule → R = ⊤)
    (hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (ρ g)) :
    (ρ.quotient T.toSubmodule hst).IsIrreducible := by
  have hne : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hnt : Nontrivial (Subrepresentation (ρ.quotient T.toSubmodule hst)) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h1 : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ∈
        (⊤ : Subrepresentation (ρ.quotient T.toSubmodule hst)).toSubmodule := trivial
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  refine ⟨fun R => ?_⟩
  let T' : Subrepresentation ρ := ⟨R.toSubmodule.comap T.toSubmodule.mkQ, by
    intro g v hv
    have := R.apply_mem_toSubmodule g hv
    exact this⟩
  have hle : T ≤ T' := by
    intro x hx
    show T.toSubmodule.mkQ x ∈ R.toSubmodule
    have h0 : T.toSubmodule.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [h0]
    exact R.toSubmodule.zero_mem
  by_cases huT : u ∈ T'.toSubmodule
  · right
    have hT' := hgen T' huT
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : y ∈ T'.toSubmodule := by rw [hT']; trivial
    exact this
  · left
    have hT' := hmax T' hle huT
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ T'.toSubmodule := hx
    rw [hT'] at hy
    have : (Submodule.Quotient.mk y : U ⧸ T.toSubmodule) = 0 := by
      rwa [Submodule.Quotient.mk_eq_zero]
    rw [this]
    exact Submodule.zero_mem _

def mkI (ρ : Representation ℂ G U) (T : Submodule ℂ U) (hst : ∀ g, T ≤ T.comap (ρ g)) :
    Representation.IntertwiningMap ρ (ρ.quotient T hst) where
  toLinearMap := T.mkQ
  isIntertwining' g := by
    ext v
    rfl

def inclI {ρ : Representation ℂ G U} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_sub {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : U) = v} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact hρ _

theorem smooth_quot {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (T : Submodule ℂ U)
    (hst : ∀ g, T ≤ T.comap (ρ g)) : IsSmooth (ρ.quotient T hst) :=
  _root_.UpperTheory.Reformulated.B.Gwb5.smooth_quot hρ T hst

end Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end GlobalTheory.CompanionTheory.SubEig
end
end

section

open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem exists_proj_sup {E : Type*} [AddCommGroup E] [Module ℝ E] (𝔨 𝔟 : Submodule ℝ E) :
    ∃ p q : E →ₗ[ℝ] E, (∀ Z, p Z ∈ 𝔨) ∧ (∀ Z, q Z ∈ 𝔟) ∧
      ∀ Z, Z - p Z - q Z ∈ 𝔨 ⊔ 𝔟 → Z - p Z - q Z = 0 := by
  let f : (𝔨 × 𝔟) →ₗ[ℝ] E := 𝔨.subtype.coprod 𝔟.subtype
  have hr : LinearMap.range f = 𝔨 ⊔ 𝔟 := by
    simp [f, LinearMap.range_coprod]
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨P, hP⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (by simp)
  have hsum : ∀ Z, ((s (P Z)).1 : E) + ((s (P Z)).2 : E) = (P Z : E) := by
    intro Z
    have h2 := LinearMap.congr_fun hs (P Z)
    have h3 := congrArg Subtype.val h2
    simpa [f] using h3
  refine ⟨𝔨.subtype ∘ₗ LinearMap.fst ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P, 𝔟.subtype ∘ₗ LinearMap.snd ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P,
    fun Z => (s (P Z)).1.2, fun Z => (s (P Z)).2.2, fun Z hZ => ?_⟩
  have hid : ∀ W (hW : W ∈ LinearMap.range f), P W = ⟨W, hW⟩ := fun W hW =>
    LinearMap.congr_fun hP ⟨W, hW⟩
  have hval : Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = Z - (P Z : E) := by
    rw [sub_sub, hsum]
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = 0
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) ∈ 𝔨 ⊔ 𝔟 at hZ
  rw [hval] at hZ ⊢
  rw [← hr] at hZ
  have h1 := hid _ hZ
  have h2 : P (Z - (P Z : E)) = P Z - P (P Z : E) := map_sub _ _ _
  have h3 : P (P Z : E) = P Z := hid _ (P Z).2
  rw [h3, sub_self] at h2
  have h4 := congrArg Subtype.val (h1.symm.trans h2)
  simpa using h4

theorem eventually_exp_mul_exp {G : Set A} (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {𝔤 𝔨 𝔟 : Submodule ℝ A} (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {V : Set A} (hV : V ∈ 𝓝 (0 : A)) (hVG : ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨p₀, q₀, hpk, hqb, hr0⟩ := exists_proj_sup 𝔨 𝔟
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap p₀
  let q : A →L[ℝ] A := LinearMap.toContinuousLinearMap q₀
  let r : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p - q
  have hr : ∀ Z, r Z = Z - p Z - q Z := fun Z => rfl
  let Φ : A → A := fun Z =>
    NormedSpace.exp (p Z) * NormedSpace.exp (q Z) * NormedSpace.exp (r Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEl : ∀ l : A →L[ℝ] A, HasStrictFDerivAt (fun Z => NormedSpace.exp (l Z)) l (0 : A) := by
    intro l
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (l 0) := by
      simpa using hE
    exact (h2.comp (0 : A) l.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := ((hEl p).mul' (hEl q)).mul' (hEl r)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hr]
    abel
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : r ⁻¹' V ∈ 𝓝 (0 : A) := by
    refine r.continuous.continuousAt.preimage_mem_nhds ?_
    simpa using hV
  have himg : Φ '' (r ⁻¹' V) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  have hneg : ∀ X ∈ 𝔤, NormedSpace.exp (-X) ∈ G := by
    intro X hX
    simpa using (h𝔤 X).1 hX (-1)
  have hcancel : ∀ X : A, NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    intro X
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  filter_upwards [himg]
  rintro g ⟨Z, hZ, rfl⟩ hgG
  have hpg : p Z ∈ 𝔤 := hk (hpk Z)
  have hqg : q Z ∈ 𝔤 := hb (hqb Z)
  have hrG : NormedSpace.exp (r Z) ∈ G := by
    have h2 := hmul _ (hneg _ hqg) _ (hmul _ (hneg _ hpg) _ hgG)
    have h3 : NormedSpace.exp (-(q Z)) * (NormedSpace.exp (-(p Z)) * Φ Z) = NormedSpace.exp (r Z) := by
      simp only [Φ]
      rw [← mul_assoc (NormedSpace.exp (-(p Z))), ← mul_assoc (NormedSpace.exp (-(p Z))), hcancel,
        one_mul, ← mul_assoc, hcancel, one_mul]
    rwa [h3] at h2
  have hr𝔤 : r Z ∈ 𝔨 ⊔ 𝔟 := hg (hVG _ hZ hrG)
  have hrz : r Z = 0 := hr0 Z hr𝔤
  refine ⟨p Z, hpk Z, q Z, hqb Z, ?_⟩
  simp [Φ, hrz]

end Banach

theorem eventually_exp_mul_exp_of_isLinRed {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hG : GlobalTheory.LinRed.IsLinRed G) (𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (hV : ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  obtain ⟨V, hV, hVG⟩ := hV
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedRing
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedSpace
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { (inferInstance : Algebra ℝ (Matrix (Fin n) (Fin n) ℂ)) with
      norm_smul_le := fun t X => by
        have : t • X = (t : ℂ) • X := by ext a b; simp
        rw [this, norm_smul]
        simp }
  exact eventually_exp_mul_exp hG.mul_mem h𝔤 hV hVG hk hb hg

end GlobalTheory.CompanionTheory.ClosedSubgroup
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.induced_two_characters_not_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | exact GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | (intros; apply GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det <;> assumption)
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def polyBall (n : ℕ) (s : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ cball s}
  mul_mem' := fun ha hb i => add_mem_cball (ha i) (hb i)
  one_mem' := fun i => by simp [cball]
  inv_mem' := fun {x} hx i => by
    have h := hx i
    simpa [cball, Valuation.map_neg] using h

def resChr (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (L : Subgroup (Multiplicative (Fin n → k))) : L →* ℂˣ :=
  (chrA k ψ a).comp L.subtype

def unipIn (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

def ann (ψ : AddChar k Circle) (n : ℕ) (t : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ a ∈ polyBall n t, ψ (a.toAdd ⬝ᵥ x.toAdd) = 1}
  mul_mem' := fun {x y} hx hy a ha => by
    rw [toAdd_mul, dotProduct_add, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  one_mem' := fun a _ => by simp
  inv_mem' := fun {x} hx a ha => by
    rw [toAdd_inv, dotProduct_neg, AddChar.map_neg_eq_inv, hx a ha, inv_one]

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : Fin (M + 2) → K :=
  Fin.cons a (Fin.cons s Y)

def tailH {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : Fin M → K := fun i => x i.succ.succ

section Chart

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR : R ⊗[F] E := inclR R (algebraMap F E (1 / 2))

def tHalf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E) : R ⊗[F] E :=
  halfR (F := F) (E := E) R * hR R σ (hypOne J) x x

def cvec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x v : Fin (M + 2) → R ⊗[F] E) :
    Fin (M + 2) → R ⊗[F] E :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (sigR R σ (x 0)) *
      (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
    (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E :=
  Fin.cons (x 0) fun j => cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))


variable {R} in
def yPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin n → Fin M → K :=
  fun j i => X j.succ i.succ.succ - X j.succ 0 * Ring.inverse (X 0 0) * X 0 i.succ.succ

def freeCell (K : Type) [CommRing K] (M n : ℕ) : Set (Fin (n + 1) → Fin (M + 2) → K) :=
  {X | IsUnit (X 0 0) ∧ LinearIndependent K (yPart X)}

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

def qH (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (t : HermR R σ 1) (s a : Fin 1 → Fin n → R ⊗[F] E) :
    HermR R σ n :=
  ⟨Matrix.of fun i j => sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
      (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j), by
    intro i j
    have ht : sigR R σ ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      t.2 0 0
    simp only [Matrix.of_apply, map_add (f := _), map_sub, map_mul, sigR_sigR R σ hσ, ht]
    ring⟩

end Chart

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.archimedean_orbital_integral_hua_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.card_range_mul_quotient_bounded_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | exact GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level <;> assumption)
end
