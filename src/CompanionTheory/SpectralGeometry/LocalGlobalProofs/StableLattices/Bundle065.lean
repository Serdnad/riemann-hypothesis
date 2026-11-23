module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Bundle001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.KSpanFinB
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
public import Formalism.RealPlaceAnalysis.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle056
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section


theorem _root_.GlobalTheory.T.rgExh_lineFacts : CompanionTheory.RgExh.Dec.N.S.LineFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradLine.lineFacts | exact GlobalTheory.CompanionTheory.GradLine.lineFacts | (intros; apply GlobalTheory.CompanionTheory.GradLine.lineFacts <;> assumption)
end

section

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.RgStart

open Formalism.REAL (GlRel KHighest IsWeight qdet)
open CompanionTheory.D.LK (IsKMod)
open CompanionTheory.RgExh

theorem monic_eval_capP : ∀ (n : ℕ) (p : ℂ[X]), p.Monic → p.natDegree = n →
    ∃ χ : Fin n → ℂ, ∀ Y : ℂ, p.eval Y = Formalism.QuantumDeterminants.capP χ Y := by
  intro n p hm hd
  let roots := p.roots.toList
  have hlen : roots.length = n := by
    simpa only [roots, Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree] using hd
  rw [← hlen]
  refine ⟨fun i => -roots[i], fun Y => ?_⟩
  calc
    p.eval Y = (p.roots.map (Y - ·)).prod :=
      (IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hm Y
    _ = (roots.map (Y - ·)).prod := by
      simp only [roots, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    _ = Formalism.QuantumDeterminants.capP (fun i => -roots[i]) Y := by
      rw [Formalism.QuantumDeterminants.capP, ← List.prod_ofFn]
      simp only [← sub_eq_add_neg]
      exact congrArg List.prod (List.ofFn_getElem_eq_map roots (Y - ·)).symm

theorem exists_char {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ u, ∃ c : ℂ, qdet E u = c • (1 : Module.End ℂ V)) :
    ∃ χ : Fin n → ℂ, ∀ Y : ℂ,
      qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
  let A := Module.End ℂ V
  let s : ℂ := ((n : ℂ) - 1) / 2
  have hexpand : ∃ c : ℕ → A, c n = 1 ∧
      ∀ Y : ℂ, qdet E (Y + s) = ∑ j ∈ Finset.range (n + 1), Y ^ j • c j := by
    cases n with
    | zero => exact ⟨fun _ => 1, rfl, fun Y => by simp [qdet, Formalism.REAL.qminor]⟩
    | succ m =>
      obtain ⟨c, _, hc, _, heval⟩ :=
        GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace A m E (-s)
      exact ⟨c, hc, fun Y => by simpa only [sub_neg_eq_add] using heval Y⟩
  obtain ⟨c, hlead, heval⟩ := hexpand
  let B : Subalgebra ℂ A := ⊥
  have hmem : ∀ j ≤ n, c j ∈ B := by
    refine fun j hj => GlobalTheory.coeff_mem_of_poly_values_mem A B.toSubmodule
      (n + 1) c (fun Y => ?_) j (Nat.lt_succ_of_le hj)
    rw [← heval]
    obtain ⟨d, hd⟩ := h (Y + s)
    exact Algebra.mem_bot.2 ⟨d, by rw [hd, Algebra.algebraMap_eq_smul_one]⟩
  have hd : ∀ j, ∃ d : ℂ, j ≤ n → c j = d • (1 : Module.End ℂ V) := fun j => by
    by_cases hj : j ≤ n
    · obtain ⟨d, hd⟩ := Algebra.mem_bot.1 (hmem j hj)
      exact ⟨d, fun _ => by rw [← hd, Algebra.algebraMap_eq_smul_one]⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose d hd using hd
  let q : ℂ[X] := ∑ j ∈ Finset.range n, C (d j) * X ^ j
  have hq : q.degree < n := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    simp only [q, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : m ≠ j := by have := Finset.mem_range.1 hj; omega
    simp [this]
  have hdg : (X ^ n + q).degree = (n : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  obtain ⟨χ, hχ⟩ := monic_eval_capP n (X ^ n + q) (monic_X_pow_add hq)
    (natDegree_eq_of_degree_eq_some hdg)
  refine ⟨χ, fun Y => ?_⟩
  have e2 : ∀ j ∈ Finset.range n, Y ^ j • c j = (d j * Y ^ j) • (1 : Module.End ℂ V) := fun j hj => by
    rw [hd j (Finset.mem_range.1 hj).le, smul_smul, mul_comm]
  change qdet E (Y + s) = _
  rw [heval Y, Finset.sum_range_succ, hlead, Finset.sum_congr rfl e2, ← hχ]
  simp only [q, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, add_smul, Finset.sum_smul]
  rw [add_comm]

section Rep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem exists_emb (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E) :
    ∃ ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ, Function.Injective ι ∧
      (∀ x, ι x ∈ CompanionTheory.D.gk.HC.KF ε σ) ∧
      ∀ a b x, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := by
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  exact ⟨Submodule.inclusion hle, Submodule.inclusion_injective hle, fun x => (hK.mem x).1 x.2,
    fun a b x => Subtype.ext (GlobalTheory.KFinIrr.smE_eq hσ hK x (hle x.2) a b)⟩

theorem exists_kType [Nontrivial H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    ∃ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨v, hkv, hv⟩ := (GlobalTheory.HcPort.kfinDense_UJC hσ).exists_mem_open Metric.isOpen_ball
    ⟨x, Metric.mem_ball_self hpos⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [Metric.mem_ball, dist_eq_norm] at hv
  obtain ⟨S, hS, hvS, hst⟩ := hkv
  have hSb : S ≠ ⊥ := fun h => hv0 (by simpa [h] using hvS)
  obtain ⟨μ, S', -, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ S hS hst hSb
  exact ⟨μ, S', hS'⟩

theorem scalar_of_commute [Nontrivial H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E)
    (T : Module.End ℂ D) (hT : ∀ a b, T * E a b = E a b * T) :
    ∃ c : ℂ, T = c • (1 : Module.End ℂ D) := by
  have hTa : ∀ a b x, T (E a b x) = E a b (T x) := fun a b x => LinearMap.congr_fun (hT a b) x
  obtain ⟨μ, S₀, hS₀⟩ := exists_kType hσ
  obtain ⟨v, hv0, -, hv⟩ := hK.hw μ S₀ hS₀
  obtain ⟨ι, hι, hKF, hc⟩ := exists_emb hσ hirr hK
  let P : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := Submodule.span ℂ
    {w | w ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ ReciprocityTheory.ChartRestriction.DS.IsKHWVec ε (ReciprocityTheory.ChartRestriction.DS.smE ε σ) μ w}
  haveI hP : FiniteDimensional ℂ P :=
    (CompanionTheory.D.gk.HC.uAdm_of CompanionTheory.D.gk.HC.K_finite_smooth_vectors) n ε H σ hσ hirr μ
  let S : Submodule ℂ D := Submodule.span ℂ {x | KHighest ε E μ x}
  have hSP : ∀ x ∈ S, ι x ∈ P := fun x hx => by
    have : S ≤ P.comap ι := Submodule.span_le.2 fun y hy => Submodule.subset_span
      ⟨hKF y, fun a => by rw [hc, hy.1 a, map_smul],
        fun a b hab he => by rw [hc, hy.2 a b hab he, map_zero]⟩
    exact this hx
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective (ι.restrict hSP) fun x y h =>
      Subtype.ext (hι (congrArg Subtype.val h))
  have hTS : ∀ x ∈ S, T x ∈ S := fun x hx => by
    have : S ≤ S.comap T := Submodule.span_le.2 fun y hy => Submodule.subset_span
      ⟨fun a => by rw [← hTa, hy.1 a, map_smul],
        fun a b hab he => by rw [← hTa, hy.2 a b hab he, map_zero]⟩
    exact this hx
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 fun h => hv0 (by
    have : v ∈ S := Submodule.subset_span hv
    simpa [h] using this)
  obtain ⟨c, hcE⟩ := Module.End.exists_eigenvalue (T.restrict hTS)
  obtain ⟨w, hw⟩ := hcE.exists_hasEigenvector
  have hwe : T (w : D) = c • (w : D) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : D) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let N : Submodule ℂ D := LinearMap.ker (T - c • (1 : Module.End ℂ D))
  have hN : ∀ x, x ∈ N ↔ T x = c • x := fun x => by
    simp [N, sub_eq_zero]
  rcases GlobalTheory.KFinIrr.kMod_irred n ε H σ D E inferInstance hσ hirr hK N (fun a b x hx => by
      rw [hN] at hx ⊢
      rw [hTa, hx, map_smul]) with h | h
  · exact absurd (by simpa [h] using (hN w).2 hwe) hw0
  · refine ⟨c, LinearMap.ext fun x => ?_⟩
    have : x ∈ N := h ▸ Submodule.mem_top
    simpa using (hN x).1 this

theorem intWt (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E) :
    IntWt ⟨D, E, hK.gl⟩ := by
  intro μ x hx0 hx a
  obtain ⟨ι, hι, hKF, hc⟩ := exists_emb hσ hirr hK
  by_contra hno
  have hne : ∀ m : ℤ, (m : ℂ) ≠ (μ a : ℂ) := fun m hm => hno ⟨m, by exact_mod_cast hm.symm⟩
  let T : Module.End ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := ReciprocityTheory.ChartRestriction.DS.smE ε σ a a
  have h1 : ι x ∈ T.eigenspace (μ a : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    change ReciprocityTheory.ChartRestriction.DS.smE ε σ a a (ι x) = _
    rw [hc]
    have : E a a x = (μ a : ℂ) • x := hx a
    rw [this, map_smul]
  have h2 : ι x ∈ ⨆ j, ⨆ (_ : j ≠ (μ a : ℂ)), T.eigenspace j := by
    have hle : Submodule.span ℂ {w : ReciprocityTheory.ChartRestriction.DS.smD ε σ | w ∈ CompanionTheory.D.gk.HC.KF ε σ ∧
        ∃ ν : Fin n → ℤ, ∀ b, ReciprocityTheory.ChartRestriction.DS.smE ε σ b b w = (ν b : ℂ) • w} ≤
        ⨆ j, ⨆ (_ : j ≠ (μ a : ℂ)), T.eigenspace j := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨-, ν, hν⟩
      have hw : w ∈ T.eigenspace (ν a : ℂ) := by
        rw [Module.End.mem_eigenspace_iff]
        exact hν a
      exact (le_iSup₂_of_le (f := fun j (_ : j ≠ (μ a : ℂ)) => T.eigenspace j) (ν a : ℂ) (hne _) le_rfl) hw
    exact hle (CompanionTheory.D.gk.HC.integral_weights n ε H σ hσ hirr _ (hKF x))
  have hz : ι x = 0 := by
    have := (Module.End.eigenspaces_iSupIndep T (μ a : ℂ))
    exact (Submodule.disjoint_def.1 this) _ h1 h2
  exact hx0 (hι (by rw [hz, map_zero]))

end Rep

theorem startMod : CompanionTheory.RgExh.Fin.StartMod := by
  intro n ε H _ _ _ σ hσ hirr hH D E hK
  obtain ⟨μ, S₀, hS₀⟩ := exists_kType hσ
  obtain ⟨v, hv0, -, -⟩ := hK.hw μ S₀ hS₀
  haveI : Nontrivial D := ⟨⟨v, 0, hv0⟩⟩
  refine ⟨⟨inferInstanceAs (Nontrivial D), GlobalTheory.KFinIrr.kMod_irred n ε H σ D E inferInstance hσ hirr hK⟩, ?_,
    intWt hσ hirr hK⟩
  exact exists_char E fun u => scalar_of_commute hσ hirr hK _ fun a b =>
    Formalism.REAL.qDetCentral _ n E hK.gl u a b

end GlobalTheory.CompanionTheory.RgStart
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFibre

theorem cech_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  intro k _ X T Z a b p q H _ _ G hG R _ t Y π f Hy κ _ _ D hD hc hac s σ hs h₁ h₂
  obtain ⟨χ, rfl⟩ : ∃ χ : R →+* k, Spec.map (CommRingCat.ofHom χ) = s :=
    ⟨(Spec.preimage s).hom, by simp⟩
  have Hx : IsPullback (π ≫ p) f a (t ≫ b) := Hy.paste_horiz H
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) Hx inferInstance
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) Hx inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have Hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  obtain ⟨F, π', g, Hs⟩ : ∃ (F : Scheme.{0}) (π' : F ⟶ Y) (g : F ⟶ Spec (CommRingCat.of k)),
      IsPullback π' g f (Spec.map (CommRingCat.ofHom χ)) := ⟨_, _, _, Hs⟩
  have hext := GlobalTheory.T.flat_bounded_acyclic_base_change R k χ (cechLB f (G.pull π) D) (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hM hI) hac
  have hF : (cechLB g ((G.pull π).pull π') fun i => π' ⁻¹ᵁ D i).Acyclic :=
    fun n => (hext n).of_iso (cechLBBaseChangeIso hM Hs hI)
  have Hu : IsPullback (π' ≫ π ≫ p) g a (Spec.map (CommRingCat.ofHom χ) ≫ t ≫ b) :=
    Hs.paste_horiz Hx
  rw [hs] at Hu
  obtain ⟨u, hu⟩ : ∃ u : F ⟶ X, u = π' ≫ π ≫ p := ⟨_, rfl⟩
  rw [← hu] at Hu
  haveI : IsIso u := Hu.isIso_fst_of_isIso
  have hua : u ≫ a = g := Hu.w.trans (Category.comp_id _)
  have he : u ≫ σ = π' ≫ π := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, Category.comp_id, hu, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, hua, Category.assoc π', Hy.w, ← Category.assoc π',
        Hs.w, Category.assoc]
  refine ⟨fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i,
    fun i => (isAffineOpen_preimage_of_isPullback Hs (hD i)).preimage_of_isIso _, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]
    rfl
  · have hN := LB.isLB_pull hG σ
    obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) F u κ
      (fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) hN
      (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
    have hD' : (fun i => u ⁻¹ᵁ inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) = fun i => π' ⁻¹ᵁ D i := funext fun i => by
      rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
      rfl
    rw [hua, hD'] at i₁
    obtain ⟨w₁, hw₁⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π π'
    obtain ⟨w₂, hw₂⟩ : ∃ w : LB.Iso ((G.pull σ).pull u) (G.pull (π' ≫ π)), w.IsGen :=
      he ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ u
    have hP := LB.isLB_pull hG (π' ≫ π)
    have i₂ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hM π') hP w₁ hw₁
    have i₃ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hN u) hP w₂ hw₂
    exact fun n => (hF n).of_iso (i₂ ≪≫ i₃.symm ≪≫ i₁)

end GlobalTheory.CompanionTheory.PointSurjFibre
end
