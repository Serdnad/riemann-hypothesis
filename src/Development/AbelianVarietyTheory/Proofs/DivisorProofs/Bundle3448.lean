module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAnyField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  first | (exact @GlobalTheory.HTUniv.main) | (exact GlobalTheory.HTUniv.main) | (intros; apply GlobalTheory.HTUniv.main  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem add_le_sum_Icc_of_lt (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) {n i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) {d : ℚ} (hd : d ≤ ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε)) :
    d + (h (i + 1) + ε) ≤ ∑ e ∈ Finset.Icc (i + 1) n, (h e + ε) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ n), Finset.sum_cons]
  have : ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Ioc (i + 1) n, (h e + ε) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => by simp only [Finset.mem_Icc, Finset.mem_Ioc] at he ⊢; omega)
      fun e _ _ => (hpos e).le
  linarith

theorem sum_Icc_le_sum_Icc_one (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) (n j : ℕ) :
    ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun e _ _ => (hpos e).le

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem two_point_induction : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair →
    GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ)
    (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m →
    IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) →
    IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) →
    (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e →
      topologicalKrullDim (closure ({z} : Set X)) = e →
      2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X))
        fun _ : Fin e => N : ℤ)) → 0 < ε →
    ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧
      ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨
        (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim
  letI := algebraΓOfHom p
  intro Δ m G N ε h x₁ x₂ hΔ hklt hm hG hNa hc₁ hc₂ hne hh hint hε
  have hpos : ∀ e, 0 < h e + ε := fun e => add_pos (hh e) hε

  have hξ : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hdimξ : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [genericPoint_closure,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hdim]

  have hn : 1 ≤ n := by
    obtain ⟨e, -, he, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n (genericPoint X) hdim
    have hen : e = n := by
      rw [hdimξ] at he; exact_mod_cast he.symm
    subst hen
    by_cases h₁ : x₁ = genericPoint X
    · exact he1 x₂ (hξ x₂) fun h₂ => hne (h₁.trans h₂.symm)
    · exact he1 x₁ (hξ x₁) h₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have key : ∀ j, j ≤ k → ∀ (D : X → ℚ) (d : ℚ), 0 ≤ d →
      d ≤ ∑ e ∈ Finset.Icc (j + 1) (k + 1), (h e + ε) → QNum p N d D →
      ((LcCut p (k + 1) (Δ + D) x₁ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
        (LcCut p (k + 1) (Δ + D) x₂ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) →
      ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 (k + 1), (h e + ε) ∧ QNum p N d D ∧
        ((LcCut p (k + 1) (Δ + D) x₁ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
          (LcCut p (k + 1) (Δ + D) x₂ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjk D d hd0 hd hQ hcut
    have hd1 := hd.trans (sum_Icc_le_sum_Icc_one h ε hpos (k + 1) j)
    rcases hcut with ⟨hc, hnk⟩ | ⟨hc, hnk⟩
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₁ x₂ j hΔ hklt hm
          hG hNa hc₁ hc₂ hne hh hint hε hQ hd0 hc hnk with h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inl ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₂ x₁ j hΔ hklt hm
          hG hNa hc₂ hc₁ hne.symm hh (fun z e hz => hint z e hz.symm) hε hQ hd0 hc hnk with
        h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inr ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'.symm

  have hlc : ∀ x, LcAt p (k + 1) (Δ + 0) x := fun x => by rw [add_zero]; exact (hklt x).lcAt
  have hdimξ' : topologicalKrullDim (closure ({genericPoint X} : Set X)) = ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hdimξ
  obtain ⟨D', d', hd'0, hd', hQ', hc'⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p (k + 1) hproj hdim Δ m G N 0
    0 (h (k + 1)) x₁ x₂ (genericPoint X) k hΔ hklt hm hG hNa (qNum_zero_zero X p hproj N) le_rfl
    hc₁ hc₂ (hlc x₁) (hlc x₂) (hξ x₁) (hξ x₂) (Or.inl rfl) hdimξ' (hh _)
    (hint (genericPoint X) (k + 1) (Or.inl (hξ x₁)) (by omega) hdimξ')
  refine key k le_rfl D' d' hd'0 ?_ hQ' hc'
  rw [Finset.Icc_self, Finset.sum_singleton]
  linarith [hε]

end GlobalTheory.PairStep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem classSums_deeper : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro g n F W Z i X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois g n F W Z i X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing g n F W Z i X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => GlobalTheory.T.extend_integral_padic_evaluation_galois p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  refine ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht, ev', f, h1, h2, h3, hf, hcs, fun σ hσ => ?_⟩
  obtain ⟨γ, hdet, hN₁, hσf⟩ := hgal σ hσ
  refine ⟨γ, fun c x => ⟨0, ?_⟩, hdet, hN₁, hσf⟩
  have hm : (Φ.mod y₀) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [smul_zero, add_zero]
  first
  | (rw [hm]; exact map_zsmul γ c x)
  | (simp only [hm]; exact map_zsmul γ c x)
  | exact map_smul γ c x

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chartSeparation_data_defined_over_centre_field : GlobalTheory.Poinc.Sep.SepSt := by
  first | exact @GlobalTheory.Poinc.Sep.sepSt | exact GlobalTheory.Poinc.Sep.sepSt | (intros; apply GlobalTheory.Poinc.Sep.sepSt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  first | exact @GlobalTheory.Mum.exists_labCover_of_pelOK | exact GlobalTheory.Mum.exists_labCover_of_pelOK | (intros; apply GlobalTheory.Mum.exists_labCover_of_pelOK <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_classicalTraits_fourierTerms_all_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → Φ.Four !![(1 : ℤ)] (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.UPoinc.four_of_classical | exact GlobalTheory.UPoinc.four_of_classical | (intros; apply GlobalTheory.UPoinc.four_of_classical <;> assumption)
end

section

namespace GlobalTheory.LaurentCohomologyVanishing

open GlobalTheory.EtC

theorem vanishing_below (q : ℕ) [NeZero q] (k : ℕ) :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
      ∀ m i : ℤ, 2 ≤ m → m < 2 + (k : ℤ) → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i) := by
  induction k with
  | zero =>
    intro A _ _ _ _ m i h2 hm
    push_cast at hm
    omega
  | succ k ih =>
    intro A _ _ hA hq m i h2 hm
    push_cast at hm
    rcases lt_or_eq_of_le (show m ≤ 2 + (k : ℤ) by omega) with h | h
    · exact ih A hA hq m i h2 h
    · subst h
      exact GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive q (2 + k) (by omega) ih A hA hq i

theorem laurent_cohomology (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (n i : ℤ) :
    (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  refine ⟨fun hn => GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian q (fun B _ _ hB hqB m j hm =>
    vanishing_below q m.toNat B hB hqB m j hm (by omega)) A hA hq n i hn, ?_⟩
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q A hA hq (i - 1)
  exact ⟨(AddEquiv.ofBijective (gmPhi q A i) (GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q A hA hq i)).symm.trans e⟩

end GlobalTheory.LaurentCohomologyVanishing
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

theorem _root_.GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.logKS_inj_mod_maximal | exact GlobalTheory.logKS_inj_mod_maximal | (intros; apply GlobalTheory.logKS_inj_mod_maximal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp

theorem relRep_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  intro p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY
  haveI := hY
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s
    (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl
  have hker' : SiegKerBy c' e := siegKerBy_pull hc' hker
  obtain ⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩ :=
    GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A) := fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)
  have hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left := fun a => GlobalTheory.SiegelPull.secPull_left hpb _
  have hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev :=
    isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')
  have hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z := fun a => Over.w (lev a)
  refine ⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩
  · rintro T g t t₁ o l hl ⟨m, hm⟩
    have h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g := ⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩
    have h2 : SiegPB (u.toSieg hsl) c' π := ⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩
    exact pb_comp (pb_comp hc' h2) h1
  · intro T t₀ t t₁ o l hl hS
    have hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R) :=
      specZIsTerminal.hom_ext _ _
    let g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) :=
      pullback.lift t₀ t hw
    have hg₁ : g₀ ≫ pullback.fst _ _ = t₀ := pullback.lift_fst _ _ _
    have hg₂ : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
    have hS' : SiegPB (o.toSieg hl) c' g₀ := pb_cancel hc' (by rw [hg₁]; exact hS)
    obtain ⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩ := hS'
    obtain ⟨z, ⟨hz, m, hm⟩, huniq⟩ := hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ
    have hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T := fun a => Over.w (l a)
    refine ⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩
    · apply hpb.1.hom_ext
      · rw [Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]
        exact hlφ a
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]
        simp
    · rintro z' ⟨h1', h2', m', hm'⟩
      have hzπ : z' ≫ π = g₀ := pullback.hom_ext (by rw [Category.assoc, h1', hg₁])
        (by rw [Category.assoc, h2', hg₂])
      refine huniq z' ⟨hzπ, m', ?_⟩
      refine GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂
        (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))
      · exact (m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _)
          (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _)
          (iso_pull_pull c'.isLB φ₂u m'.φ₂)
      · show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left
        rw [← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
end
end
