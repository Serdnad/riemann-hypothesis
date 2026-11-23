module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  first | (exact @GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (exact GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (intros; apply GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.isNoetherianRing_stalk {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (z₁ : X₁.M.Z) : IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  have := X₁.M.lft
  have : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  infer_instance

theorem four_of_classical : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  intro g n F W Z i X₁ p _ z₁ Φ hW h y₀ N₀
  obtain ⟨N, hN, hd, k, Q, t, B, _, _, _, _, _, 𝔷, hinj, hfix, hmax, hk, hu, ht, hc⟩ :=
    GlobalTheory.T.thetaFourier_classSums_deeper_finite_extension g n F W Z i X₁ p z₁ Φ h y₀ (N₀ + 1)
  have := X₁.normal.isDomain_stalk z₁
  have := X₁.normal.isIntegrallyClosed_stalk z₁
  have := X₁.isNoetherianRing_stalk z₁
  have hu' : ∀ y, @IsUnimodMod ℤ _ (Φ.X y₀) (Φ.X y) _ (Φ.mod y₀) _ (Φ.mod y) N (k y) := fun y => by
    convert hu y <;> exact Subsingleton.elim _ _
  exact ⟨N, by omega, hd, k, Q, t, hk, hu', ht,
    OrbTrace.orbitSums_of_classSums ℤ id g p _ Φ 8 W _ N y₀ k Q t B hinj hfix 𝔷 hmax (by omega) hW hu' hc⟩

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Has D) := by
  first | exact @GlobalTheory.Mum.has_of_base | exact GlobalTheory.Mum.has_of_base | (intros; apply GlobalTheory.Mum.has_of_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryApproxPoincareSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∃ d : ℕ, 1 ≤ d ∧ UApproxAt X₁ φ d := by
  first | exact @GlobalTheory.UPoinc.exists_uApproxAt | exact GlobalTheory.UPoinc.exists_uApproxAt | (intros; apply GlobalTheory.UPoinc.exists_uApproxAt <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.gm_cohomology_strictlyHenselian) | (exact GlobalTheory.gm_cohomology_strictlyHenselian) | (intros; apply GlobalTheory.gm_cohomology_strictlyHenselian  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  first | exact @GlobalTheory.LogKSAssembly.hasLogKS | exact GlobalTheory.LogKSAssembly.hasLogKS | (intros; apply GlobalTheory.LogKSAssembly.hasLogKS <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hlc hNamp hnum
    hx₁ hx₂ hne hh hvol hsum
  set S : ℚ := ∑ e ∈ Finset.Icc 1 n, h e with hS
  set ε : ℚ := (ρ - S) / (n + 1) with hε
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hn1
  have h1 : ((n : ℚ) + 1) * ε = ρ - S := by rw [hε]; field_simp
  have hsplit : ∑ e ∈ Finset.Icc 1 n, (h e + ε) = S + n * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [hS]
  obtain ⟨D, d, hd, hQ, hcase⟩ := GlobalTheory.T.twoPoint_induction_kltPair_separation hP hNV hNef X p n hproj hdim Δ m G N ε h x₁ x₂
    hΔ hklt hm hlc hNamp hx₁ hx₂ hne hh hvol hεpos
  have hdρ : d < ρ := by
    have h2 : (n : ℚ) * ε + ε = ρ - S := by rw [← h1]; ring
    linarith
  rcases hcase with ⟨hlc1, hnk2⟩ | ⟨hlc2, hnk1⟩
  · obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₁ x₂ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₁ hne hlc1 hnk2
    exact ⟨s, Or.inl ⟨hs1, hs2⟩⟩
  · obtain ⟨s, hs2, hs1⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₂ x₁ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₂ (Ne.symm hne) hlc2 hnk1
    exact ⟨s, Or.inr ⟨hs2, hs1⟩⟩
end
