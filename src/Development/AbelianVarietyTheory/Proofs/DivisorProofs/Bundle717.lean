module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle683
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLatticeFamilyRetypePeriodType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem kerReps_transport : ∀ (K : Type) [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (a : K) (S : Finset ℂ), IsTr ι Λ₀ Λ₁ T → a ≠ 0 → (∀ x x', T x x' → T (a * x) (a * x')) → IsKerReps Λ₀ (ι a) S → ∃ (φ : ℂ → ℂ) (S' : Finset ℂ), IsKerReps Λ₁ (ι a) S' ∧ Set.BijOn φ S S' ∧ ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ ι k' = φ P ∧ T k k' := by
  intro K _ ι Λ₀ Λ₁ T a S hT ha hmul hS
  classical
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  obtain ⟨hS1, hS2, hS3⟩ := hS

  have hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k' := by
    intro P hP
    obtain ⟨b, hb⟩ := hT.rat₀ _ (hS1 P hP).1
    obtain ⟨k', hk'⟩ := hT.left (b / a)
    refine ⟨b / a, k', ?_, hk'⟩
    rw [map_div₀, hb]; field_simp
  choose! k k' hk hT' using hex
  set φ : ℂ → ℂ := fun P => ι (k' P) with hφ

  have himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice := by
    intro P hP
    have h1 := hT.mem_iff _ _ (hmul _ _ (hT' P hP))
    have h2 := hT.mem_iff _ _ (hT' P hP)
    rw [map_mul, map_mul, hk P hP] at h1
    rw [hk P hP] at h2
    exact ⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩
  have hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q := by
    intro P hP Q hQ h
    have h1 := hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))
    rw [map_sub, map_sub, hk P hP, hk Q hQ] at h1
    exact hS2 P hP Q hQ (h1.mpr h)
  refine ⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP),
    fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact himg P hP
  · intro P' hP' Q' hQ' h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hQ'
    rw [hdiff P hP Q hQ h]
  · intro z hz hz'
    obtain ⟨c, hc⟩ := hT.rat₁ _ hz
    have hzc : ι (c / a) = z := by rw [map_div₀, hc]; field_simp
    obtain ⟨m, hm⟩ := hT.right (c / a)
    have h1 := hT.mem_iff _ _ (hmul _ _ hm)
    have h2 := hT.mem_iff _ _ hm
    rw [map_mul, map_mul, hzc] at h1
    rw [hzc] at h2
    obtain ⟨P, hP, hmP⟩ := hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))
    refine ⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩
    have h3 := hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))
    rw [map_sub, map_sub, hk P hP, hzc] at h3
    exact h3.mp hmP
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP')
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact ⟨k P, k' P, hk P hP, rfl, hT' P hP⟩

end GlobalTheory.WpFam
end

section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem mem_smul_top_iff_wSub {p : ℕ} [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (x : D.La) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) ↔ x ∈ wSub D w0 r := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => add_mem hu hv)
    exact Submodule.subset_span ⟨c, hc, z, rfl⟩
  · intro hx
    suffices H : ∀ b : D.O, b • x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) by simpa using H 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [smul_smul, ← Algebra.commutes, ← smul_smul]
      exact Submodule.smul_mem_smul (M := D.La) hc Submodule.mem_top
    | zero => intro b; rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => intro b; rw [smul_add]; exact add_mem (hu b) (hv b)
    | smul a u _ hu => intro b; rw [smul_smul]; exact hu (b * a)

theorem latQuot_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
    w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  intro p _ D w0 r hw
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := projective_La_int D
  haveI := D.finLa
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  obtain ⟨g, hs, hk⟩ := GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq w0 hw r _ (GlobalTheory.T.finrank_La_ringOfIntegers' D)
  refine ⟨g.toAddMonoidHom, hs, fun c x => ?_, fun x => ?_⟩
  · show g (c • x) = _
    rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  · show g x = 0 ↔ _
    rw [hk]
    exact mem_smul_top_iff_wSub D w0 r x

end GlobalTheory.UPel.HT.EtLev
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct


theorem _root_.GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F), c ≠ 0 → (∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) → ∀ v : epsPtR x ⟶ o.A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem) | (exact GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem) | (intros; apply GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_perCoord : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  first | exact @GlobalTheory.PerCoordU.perCoord_exists | exact GlobalTheory.PerCoordU.perCoord_exists | (intros; apply GlobalTheory.PerCoordU.perCoord_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphic_lattice_family_retype_periodType : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → b₀ ∈ B → (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → IsPeriod D ρ (P b₀) → (∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ ∀ a : O, ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ x, P b (a • x) = M *ᵥ P b x) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ (a : O) x, h b *ᵥ P b (a • x) = ρ a *ᵥ (h b *ᵥ P b x) := by
  first | exact @GlobalTheory.PELU.Retype.retype | exact GlobalTheory.PELU.Retype.retype | (intros; apply GlobalTheory.PELU.Retype.retype; all_goals assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_fin_span_of_cover {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by
  have hsp : Ideal.span B = ⊤ := by
    rw [← T.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hB x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hsp
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i ↦ hFB (F.equivFin.symm i).2⟩
  rw [eq_top_iff, ← hF]
  exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩

theorem le_basicOpen_of_isUnit_mp {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    {T S : AffOp X} (u : T ⟶ S) (f : (OAff s).obj T) (hu : IsUnit (mp (OAff s) u f)) :
    S.unop.1 ≤ X.basicOpen (show Γ(X, T.unop.1) from f) := by
  change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op
    (show Γ(X, T.unop.1) from f)) at hu
  have h1 := Scheme.basicOpen_of_isUnit X hu
  rw [Scheme.basicOpen_res] at h1
  rw [← h1]; exact inf_le_right

theorem cohO_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  intro R _ X s P _ G hG h1 h2
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : Pᵒᵖ) (v : T ⟶ hG.functor.op.obj t) (w : hG.functor.op.obj t ⟶ S), v ≫ w = u := by
    intro T
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover T.unop
      {f | ∃ a, X.basicOpen f ≤ (G a).1 ∧ (G a).1 ≤ T.unop.1} (fun x hx ↦ by
        obtain ⟨a, hxa, haT⟩ := h1 T.unop x hx
        obtain ⟨f, hf, hxf⟩ := T.unop.2.exists_basicOpen_le (V := (G a).1) ⟨x, hxa⟩ hx
        exact ⟨f, ⟨a, hf, haT⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
    obtain ⟨a, hfa, haT⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op a, (homOfLE (show G a ≤ T.unop from haT)).op,
      (homOfLE (show S.unop ≤ G a from hS.trans hfa)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  have hdir : ∀ (t₁ t₂ : Pᵒᵖ) (S : AffOp X), (hG.functor.op.obj t₁ ⟶ S) → (hG.functor.op.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (hG.functor.op.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS₁ : S.unop.1 ≤ (G t₁.unop).1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G t₂.unop).1 := leOfHom a₂.unop
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover S.unop
      {f | ∃ c, c ≤ t₁.unop ∧ c ≤ t₂.unop ∧ X.basicOpen f ≤ (G c).1} (fun x hx ↦ by
        obtain ⟨c, hc₁, hc₂, hxc⟩ := h2 t₁.unop t₂.unop x (hS₁ hx) (hS₂ hx)
        obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := (G c).1) ⟨x, hxc⟩ hx
        exact ⟨f, ⟨c, hc₁, hc₂, hf⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂, hfc⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op c, ⟨(homOfLE hc₁).op⟩, ⟨(homOfLE hc₂).op⟩,
      ⟨(homOfLE (show S'.unop ≤ G c from hS.trans hfc)).op⟩⟩
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) hG.functor.op H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) hG.functor.op H hcov hdir
  refine ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩, ?_⟩
  intro h0 g hg0
  have hcomp : ∀ ⦃t t' : Pᵒᵖ⦄ (a : t ⟶ t'), g t' = mp (OAff s) (hG.functor.op.map a) (g t) := by
    intro t t' a
    have e : d0 (hG.functor.op ⋙ OAff s) g t t' a = 0 := by rw [hg0]; rfl
    rw [amitsur_d0_apply] at e
    exact sub_eq_zero.1 e
  obtain ⟨g1, hg1c, hg1e⟩ := _root_.GlobalTheory.compat_family_extend (OAff s) hG.functor.op hs hg g hcomp
  have hd : d0 (OAff s) g1 = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg1c φ, sub_self]
    rfl
  obtain ⟨r, hr, huniq⟩ := h0 g1 hd
  refine ⟨r, fun t ↦ ?_, fun r' hr' ↦ huniq r' fun T ↦ ?_⟩
  · rw [← hg1e t]; exact hr _
  · refine sub_eq_zero.1 (hs T _ fun t u ↦ ?_)
    rw [map_sub, ← hg1c u, hg1e t, hr' t, AlgHom.commutes]
    exact sub_self _

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Helpers

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type} [Category.{0} C] [Category.{0} C']

theorem pOm_wsum (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (u v : Fin n → Glob1 F) {T T' : C} (w : T ⟶ T') :
    pOm F 2 w (wsum F u v T) = wsum F u v T' := by
  unfold wsum

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [pOm_wedge, ← (u k).2 w, ← (v k).2 w]

theorem qOm_wsum {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F')
    {n : ℕ} (u v : Fin n → Glob1 F) (T : C') :
    qOm m 2 T (wsum F u v (m.G.obj T)) =
      wsum F' (fun k ↦ pullGlob1 m (u k)) (fun k ↦ pullGlob1 m (v k)) T := by
  unfold wsum

  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ qOm_wedge m _ _

end Helpers

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem obRel_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h x n u v hx
  obtain ⟨f, ω, hfx, hconn, hcurv⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  have e1 := isPullO_pullHO1 h x
  rw [IsPullO, ← hf', ← hfx, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e1
  obtain ⟨b, hb⟩ := e1
  have hb' : ∀ (t t' : (Pair φ)ᵒᵖ) (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a - (b t' - mp (OPair φ s') a (b t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hb t) t') a
    simp only [Pi.sub_apply, amitsur_d0_apply] at e
    linear_combination e
  let ω'' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] :=
    fun t ↦ q1 (pairPull h) t (ω _) - D R' _ (b t)
  let κ : A1 (OAff s') := fun T T' ψ ↦ D R' _ (f'.1 T T' ψ)
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (c : T' ⟶ T''),
      κ T T'' (a ≫ c) = p1 (OAff s') c (κ T T' a) + κ T' T'' c := by
    intro T T' T'' a c
    simp only [κ]
    rw [Z1.comp f', map_add (f := _), p1_D]
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      κ _ _ ((pairFst φ).map a) = ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) := by
    intro t t' a
    have e0 := hconn ((pairSnd φ).map a)
    have e : q1 (pairPull h) t' (ω _) = p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) +
        D R' _ ((pairPull h).α t' (f.1 _ _ ((pairSnd φ).map a))) := by
      rw [← cechDeRhamCoefMapOneForms_naturality, ← cechDeRhamCoefMapOneForms_D, ← map_add (f := _)]; exact congrArg _ e0
    have k1 : κ _ _ ((pairFst φ).map a) = D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) -
        (D R' _ (b t') - D R' _ (mp (OPair φ s') a (b t))) := by
      simp only [κ]
      rw [show f'.1 _ _ ((pairFst φ).map a) = ((pairRes φ s').pullbackOneCocycle f').1 t t' a from rfl, hb' t t' a,
        map_sub, map_sub] <;> rfl
    have k3 : p1 (OPair φ s') a (D R' _ (b t)) = D R' _ (mp (OPair φ s') a (b t)) :=
      p1_D _ _ _
    have key : ∀ {M : Type} [AddCommGroup M] (df da db dm q' q pq pd : M), df = da - (db - dm) →
        q' = pq + da → pd = dm → df = (q' - db) - (pq - pd) := by
      intros; subst_vars; abel
    rw [show ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) = (q1 (pairPull h) t' (ω _) - D R' _ (b t')) -
      (p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) -
        p1 (OPair φ s') a (D R' _ (b t))) from by simp only [ω'', map_sub] <;> rfl]
    exact key _ _ _ _ _ (0 : Ω[(OAff s').obj ((pairFst φ).obj t')⁄R']) _ _ k1 e k3
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ) hs1 hg1
    κ hκ ω'' hθ'
  have key2 : ∀ {M : Type} [AddCommGroup M] (k A PA C PC PAC : M), k = A - PA → k = C - PC →
      PAC = PA - PC → A - C = PAC := by
    intro M _ k A PA C PC PAC h1 h2 h3
    subst h3
    exact sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)
  let δ : Glob1 (OPair φ s') := ⟨fun t ↦ θ ((pairFst φ).obj t) - ω'' t, fun t t' a ↦
    key2 _ _ _ _ _ _ (hθ ((pairFst φ).map a)) (hθ' a) (map_sub _ _ _)⟩
  obtain ⟨β, hβ⟩ := (pairRes_bijective φ s').2.1.2 δ
  have hβt : ∀ t, β.1 ((pairFst φ).obj t) = θ ((pairFst φ).obj t) - ω'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _).symm.trans (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) hβ)
  refine ⟨f', fun T ↦ θ T - β.1 T, hf', fun T T' ψ ↦ ?_, fun T ↦ ?_⟩
  · have key3 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB : M), k = A - PA → B = PB →
        A - B = (PA - PB) + k := by
      intros; subst_vars; abel
    rw [map_sub]
    exact key3 _ _ _ _ _ (hθ ψ) (β.2 ψ)
  · refine sub_eq_zero.1 (hs2 T _ fun t w ↦ ?_)
    have key4 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB O : M), k = A - PA → B = PB → B = A - O →
        PA - PB = O - k := by
      intros; subst_vars; abel
    have key5 : ∀ (B : Type) [CommRing B] [Algebra R' B] (y : Ω[B⁄R']) (c : B),
        dOne R' B (y - D R' B c) = dOne R' B y := fun B _ _ y c ↦ by rw [map_sub, dOne_D, sub_zero]
    have c1 : p1 (OAff s') w (θ T - β.1 T) = ω'' t - D R' _ (f'.1 _ _ w) := by
      rw [map_sub]; exact key4 _ _ _ _ _ _ (hθ w) (β.2 w) (hβt t)
    have e1 : ∀ (z : Fin n → GlobForm s) k, pullGlob1 (pairPull h) (z k) =
        pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (z k)) := fun z k ↦ isPullForm_pullForm h (z k)
    have c2 : dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t) = wsum (OAff s')
        (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t) := by
      calc dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t)
          = dOne R' ((OPair φ s').obj t) (q1 (pairPull h) t (ω ((pairSnd φ).obj t))) := key5 _ _ _
        _ = qOm (pairPull h) 2 t (dOne R ((OAff s).obj ((pairSnd φ).obj t)) (ω ((pairSnd φ).obj t))) :=
          (qOm_dOne _ _).symm
        _ = qOm (pairPull h) 2 t (wsum (OAff s) u v ((pairSnd φ).obj t)) := by rw [hcurv]
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairPull h) (u k)) (fun k ↦ pullGlob1 (pairPull h) (v k)) t :=
          qOm_wsum _ _ _ _
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (u k)))
            (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (v k))) t := by
          simp only [e1 u, e1 v]
        _ = qOm (pairRes φ s') 2 t (wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
            (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t)) := (qOm_wsum _ _ _ _).symm
        _ = _ := qOm_restrict _ _ _ _
    have c3 := pOm_wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
      (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) w
    rw [map_sub, pOm_dOne, c1, c3, key5, c2, sub_self]

end GlobalTheory.AbCoh
end
