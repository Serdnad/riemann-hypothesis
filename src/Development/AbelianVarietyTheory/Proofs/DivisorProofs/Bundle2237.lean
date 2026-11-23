module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle700
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

theorem exists_ext (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    ∃ τ' : F →+* ℂ, ∀ c : 𝓞 F, τ' (c : F) = τ c := by
  have hinj : Function.Injective τ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker τ) hne (by simpa [RingHom.mem_ker] using hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, map_intCast] at hn
    simpa using hn
  refine ⟨IsFractionRing.lift hinj, fun c => ?_⟩
  exact IsFractionRing.lift_algebraMap hinj c

theorem root_cases {r z : ℂ} {tr nm : ℤ} (hd : tr ^ 2 - 4 * nm < 0) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (z ≠ r ↔ (starRingEnd ℂ) z = r) := by
  have hc : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hfac : ∀ x : ℂ, x ^ 2 - tr * x + nm = 0 → x = r ∨ x = tr - r := by
    intro x hx
    have : (x - r) * (x - (tr - r)) = 0 := by linear_combination hx - hr
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    have him : r.im = 0 := Complex.conj_eq_iff_im.1 h
    have hre := congrArg Complex.re hr
    have himr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [himr] at hre
    simp [sq] at hre
    have : ((2 * r.re - tr) ^ 2 : ℝ) = (tr : ℝ) ^ 2 - 4 * nm := by linear_combination 4 * hre
    have h2 : ((tr : ℝ) ^ 2 - 4 * nm) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * r.re - tr)]
  have hcr : (starRingEnd ℂ) r = tr - r := (hfac _ hc).resolve_left hne
  constructor
  · intro h
    have : z = tr - r := (hfac z hz).resolve_left h
    rw [this, ← hcr]; simp
  · intro h hzr
    rw [hzr] at h
    exact hne h

theorem lie_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  intro p _ D R _ b N σ ρ o h hL D' t Q e hU
  classical
  choose τ hτ using fun i => exists_ext D.F (σ.comp (b.t i))
  have hτ' : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c => hτ i c
  obtain ⟨hrank, hcov⟩ := GlobalTheory.T.eigenspace_dimension_of_uniformization p D R b N σ ρ o h hL D' t Q e hU τ hτ'
  have hsum := GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul p D D' ρ Q hU.2.1
  set r := σ b.ρ with hrdef
  have hr : r ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hω : (D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hτω : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have := congrArg (fun x : 𝓞 D.F => τ' (x : D.F)) hω
    simpa using this
  have key : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ≠ r ↔ ((starRingEnd ℂ).comp τ') (D.ω : D.F) = r :=
    fun τ' => root_cases D.disc_neg hr (hτω τ')

  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := hτ' i x
      have h2 := hτ' j x
      rw [hij] at h1
      simp [RingHom.mem_ker, ← h1, ← h2]
    rw [b.comax i j hne] at hle
    have : (1 : R) ∈ RingHom.ker σ := hle Submodule.mem_top
    simp [RingHom.mem_ker] at this
  have hτA : ∀ i, τ i (D.ω : D.F) = r := fun i => by rw [hτ', b.t_ω]
  set d : (D.F →+* ℂ) → ℕ := fun τ' => Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ') with hd

  have hzero : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = r → τ' ∉ Finset.univ.image τ → d τ' = 0 := by
    intro τ' h1 h2
    have hbot : eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = r • u := by
        have := hu D.ω
        rw [h1] at this
        exact this
      have hmem := hcov u hu'
      have hle : (⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) ≤ ⨆ τ'' ∈ Finset.univ.image τ, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'' := by
        refine iSup_le fun i => ?_
        exact le_biSup (fun τ'' => eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'') (Finset.mem_image_of_mem τ (Finset.mem_univ i))
      have := (GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) _ τ' h2).le_bot ⟨hu, hle hmem⟩
      simpa using this
    simp [hd, hbot]
  have hA : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ i, (D.m : ℂ) * σ (b.t i c) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hA' : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) =
      ∑ i, (D.m : ℂ) * (starRingEnd ℂ) (σ (b.t i c)) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hconj : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) := by
    intro c
    refine Finset.sum_nbij' (fun τ' => (starRingEnd ℂ).comp τ') (fun τ' => (starRingEnd ℂ).comp τ') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have := (key x).1 (by simpa using hx)
      simpa using this
    · intro x hx
      have hx' : x (D.ω : D.F) = r := by simpa using hx
      have : ¬ ((starRingEnd ℂ).comp x) (D.ω : D.F) = r := by
        exact fun h => (key x).2 h hx'
      simpa using this
    · intro x _; ext; simp
    · intro x _; ext; simp
    · intro x _; simp
  intro c
  have htr : (ρ (algebraMap (𝓞 D.F) D.O c)).trace = ∑ τ' : D.F →+* ℂ, (d τ' : ℂ) * τ' (c : D.F) := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) c
  rw [htr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r)]
  have hB : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), ((D.m : ℂ) * D.n * τ' (c : D.F) -
        (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F)) := by
    refine Finset.sum_congr rfl fun τ' _ => ?_
    have := hsum τ'
    have h' : (d τ' : ℂ) + d ((starRingEnd ℂ).comp τ') = D.m * D.n := by exact_mod_cast this
    linear_combination τ' (c : D.F) * h'
  rw [hB, Finset.sum_sub_distrib, hconj c, hA c, hA' c]
  have e1 : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.m : ℂ) * D.n * τ' (c : D.F) =
      D.m * ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.n : ℂ) * τ' (c : D.F) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  simp only [← Finset.mul_sum]
  ring

end GlobalTheory.UPel.HT.LieType
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRepD.archRepD | exact GlobalTheory.ArchRepD.archRepD | (intros; apply GlobalTheory.ArchRepD.archRepD <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem twOrb_globFn_eq_finprod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) = ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  have hTB := fun w : Pl E => GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w
  have hKo : ∀ w : Pl E, IsOpen (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.1
  have hKc : ∀ w : Pl E, IsCompact (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.2.1
  let p : ∀ i : S, finU (E := E) (n := n) →* UL n i.1 := fun i =>
    ((cLoc i.1).comp (finU (E := E) (n := n)).subtype).codRestrict (UL n i.1) (fun x => GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)
  have hp : ∀ (i : S) (x : finU (E := E) (n := n)), p i x = toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := by
    intro i x
    unfold toSub
    rw [dif_pos (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)]
    rfl
  have hδ : ∀ i : S, p i (finPt γ) = locPt i.1 γ := fun i => (hp i _).trans (GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint E hU n γ i.1)
  have hsep : ∀ w : Pl E, (locPt w γ).1.val.charpoly.Separable := by
    intro w
    rw [GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational E hU n γ w]
    show ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) |>.charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hγ.map
  have hlev : ∀ w : Pl E, IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    fun w => ⟨hKo w, le_rfl, fun k hk => hk⟩
  have hglob : globFn S f = fun x => ∏ᶠ i : S, f i.1 (p i x) := by
    funext x
    unfold globFn
    exact (finprod_subtype_eq_finprod_cond (f := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n)))) (fun w => w ∈ S)).symm.trans
      (finprod_congr fun i => by rw [hp])
  have hK : ∀ x : finU (E := E) (n := n), x ∈ globLev S (KL n) ↔ ∀ i : S, p i x ∈ KL n i.1 := by
    intro x
    unfold globLev
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · intro h i
      obtain ⟨k, hk, hke⟩ := h i.1 i.2
      have : p i x = k := Subtype.ext hke.symm
      rw [this]; exact hk
    · intro h w hw
      exact ⟨p ⟨w, hw⟩ x, h ⟨w, hw⟩, rfl⟩
  rw [hglob]
  have hmain := GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod S (finU (E := E) (n := n)) (fun i : S => UL n i.1) p (globLev S (KL n)) (fun i => KL n i.1) (finPt γ)
    (fun i => f i.1)
    (fun i => by
      have hfun : (p i : finU (E := E) (n := n) → UL n i.1) = fun x : finU (E := E) (n := n) => toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := funext (hp i)
      rw [hfun]; exact GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup E hU n i.1)
    (fun x y h => GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq E hU n S hS x y (fun w hw => by rw [← hp ⟨w, hw⟩, ← hp ⟨w, hw⟩]; exact h ⟨w, hw⟩))
    (fun y hy => by
      let y' : ∀ w : Pl E, UL n w := fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 1
      have hy' : ∀ᶠ w in cofinite, y' w ∈ KL n w := by
        rw [Filter.eventually_cofinite] at hy ⊢
        refine (hy.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [y', hwS] using hw, rfl⟩
        · exact absurd (by simp only [y', dif_neg hwS]; exact one_mem _) hw
      obtain ⟨x, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family E hU n S hS y' hy'
      exact ⟨x, fun i => by rw [hp, hx i.1 i.2]; simp [y', i.2]⟩)
    (fun x => by
      have h := GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral E hU n x
      rw [Filter.eventually_cofinite] at h ⊢
      refine (h.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      rwa [← hp])
    hK
    (fun C hC hCK => by
      let C' : ∀ w : Pl E, Set (UL n w) := fun w => if hw : w ∈ S then C ⟨w, hw⟩ else (KL n w : Set (UL n w))
      have hC' : ∀ᶠ w in cofinite, C' w = KL n w := by
        rw [Filter.eventually_cofinite] at hCK ⊢
        refine (hCK.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [C', hwS] using hw, rfl⟩
        · exact absurd (by simp only [C', dif_neg hwS]) hw
      have h := GlobalTheory.T.isCompact_definiteUnitary_restricted_product E hU n S hS C' (fun w => by
        by_cases hw : w ∈ S
        · simp only [C', dif_pos hw]; exact hC _
        · simp only [C', dif_neg hw]; exact hKc w) hC'
      convert h using 1
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx w hw
        have := hx ⟨w, hw⟩
        rw [hp] at this
        simpa [C', hw] using this
      · intro hx i
        have := hx i.1 i.2
        rw [hp]
        simpa [C', i.2] using this)
    (fun i => hKc i.1)
    (fun i => by rw [hδ]; exact GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable E hU n i.1 (locPt i.1 γ) (hsep i.1))
    (fun i x => by rw [hδ]; exact (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).1 x)
    (fun i x => GlobalTheory.T.rightStabilizer_conj_biinvariant_finiteIndex (UL n i.1) (KL n i.1) (K' i.1) (f i.1) (p i (finPt γ)) (hKc i.1) (hK'.1 i.1).1
      (hK'.1 i.1).2.1 (hf.1 i.1).2 x)
    (fun i => by
      rw [hδ]
      exact GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj (UL n i.1) (twCent (MonoidHom.id (UL n i.1)) (locPt i.1 γ)) (KL n i.1) (locPt i.1 γ) (f i.1)
        (hKc i.1) (hf.1 i.1).1 (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).2)
    (by
      have hgood := (GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact E hU n γ hγ).and (hf.2.and ((GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral E hU n hn γ hγ).and (GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ)))
      rw [Filter.eventually_cofinite] at hgood ⊢
      refine (hgood.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      intro h
      apply hi
      rw [hδ]
      exact h)
  rw [hmain]
  simp_rw [hδ]
  exact finprod_subtype_eq_finprod_cond (f := fun w => twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) (fun w => w ∈ S)

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isHecke_productOfLocalTestFunctions_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → IsHecke (globLev S K') (globFn S f) := by
  first | exact @GlobalTheory.BCT.GlobHecke.isHecke_globFn | exact GlobalTheory.BCT.GlobHecke.isHecke_globFn | (intros; apply GlobalTheory.BCT.GlobHecke.isHecke_globFn <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  first | exact @GlobalTheory.TrMultSep.separation_of_iwahoriTrace | exact GlobalTheory.TrMultSep.separation_of_iwahoriTrace | (intros; apply GlobalTheory.TrMultSep.separation_of_iwahoriTrace <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixG_eq_unipRad_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ u ∈ unipRad σ J C, ∃ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), g = u * x ∧ (g ∈ ratPts σ J → x ∈ ratPts σ J) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  obtain ⟨g₀, b, hgZ, -, -, hrat⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF g hg
  obtain ⟨e, -, he, herat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  obtain ⟨hxC, hxD, hxZ⟩ := he g₀
  set x := e g₀ with hx
  refine ⟨g * x⁻¹, ?_, x, ⟨hxC, hxD⟩, by group, fun h => herat g₀ (hrat h)⟩
  rw [GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame F E σ n J j m C D Z J₀ hF]
  have hxiC : x⁻¹ ∈ fixG σ J C := inv_mem hxC
  have hC' : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C := hxiC
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg

  have hxiZ : (matHom _ σ J x⁻¹).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀⁻¹).1 := by
    have h1 : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) * (matHom _ σ J₀ g₀⁻¹).1
        = (matHom _ σ J x⁻¹).1 * (adMat F Z * (matHom _ σ J₀ g₀).1) * (matHom _ σ J₀ g₀⁻¹).1 := by rw [hxZ]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨?_, b * (matHom _ σ J₀ g₀⁻¹).1, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hC', hgC]
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hxiZ, ← Matrix.mul_assoc, hgZ, Matrix.add_mul, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj


theorem _root_.GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  first | exact @GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar | exact GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar | (intros; apply GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

theorem _root_.GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  first | exact @GlobalTheory.FlatCM.ImageDeg.deg_images | exact GlobalTheory.FlatCM.ImageDeg.deg_images | (intros; apply GlobalTheory.FlatCM.ImageDeg.deg_images <;> assumption)
end
