module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialEvalCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle189
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNatural
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle190
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.restrict_graded_pull_natural : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) := by
  first | exact @GlobalTheory.CompanionTheory.OpenThick.open_thick | exact GlobalTheory.CompanionTheory.OpenThick.open_thick | (intros; apply GlobalTheory.CompanionTheory.OpenThick.open_thick <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_split_range_iso_of_interval : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  first | exact @GlobalTheory.CompanionTheory.GrPiece.main | exact GlobalTheory.CompanionTheory.GrPiece.main | (intros; apply GlobalTheory.CompanionTheory.GrPiece.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_twisting_line_data_projective : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N), ∃ D : E.LineData X, IsTautologicalLineAt D N i := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | exact GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoInteg

theorem away_val_mk {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (n : ℕ) (x : MvPolynomial (Fin (N + 1)) K) (hx : x ∈ grK K N (n • D)) :
    (HomogeneousLocalization.Away.mk (grK K N) hg n x hx).val =
      algebraMap _ (Localization.Away g) x * (IsLocalization.Away.invSelf g : Localization.Away g) ^ n := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  have h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1 :=
    IsLocalization.Away.mul_invSelf g
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]

theorem away_relation {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (r • D))
    (c : ℕ → MvPolynomial (Fin (N + 1)) K) (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D))
    (F : MvPolynomial (Fin (N + 1)) K) (hF : F ∈ grK K N ((s * r) • D))
    (hFe : F = f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l) :
    HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ s +
      ∑ l ∈ Finset.range s, HomogeneousLocalization.Away.mk (grK K N) hg _ (c l) (hc l) *
        HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ l =
      HomogeneousLocalization.Away.mk (grK K N) hg _ F hF := by
  have val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g),
      (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val := fun t u =>
    map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_mul, val_sum, away_val_mk]
  rw [hFe]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm s r]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have : s * r = (s - l) * r + r * l := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [this, pow_add, mul_pow, ← pow_mul]
    ring

theorem rel_mem {K : Type} [Field K] {N : ℕ} {D : ℕ} (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f ∈ grK K N (r • D)) (c : ℕ → MvPolynomial (Fin (N + 1)) K)
    (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D)) :
    f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l ∈ grK K N ((s * r) • D) := by
  have hf' : f.IsHomogeneous (r • D) := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  refine add_mem ?_ (sum_mem fun l hl => ?_)
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    convert hf'.pow s using 1
    simp only [smul_eq_mul]
    ring
  · have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    rw [MvPolynomial.mem_homogeneousSubmodule]
    convert ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    ring

theorem isIntegral_torusS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  intro K _ X N d e i y hy V hV he q hq hfin S hS ht
  letI := (strV q V).toAlgebra
  intro a
  have hg := yS_mem y hy S
  obtain ⟨r, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grK K N) hg a
  by_cases hS0 : S.card = 0
  ·
    have hf0 : f.IsHomogeneous 0 := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      simpa [hS0] using this
    have hfC : f = MvPolynomial.C (AddMonoidAlgebra.coeff f 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)
    have hc : (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card) := by
      rw [hS0, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_C _ _
    have hmem := GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc
    have hfe : MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K) = f := by
      rw [MvPolynomial.aeval_C]
      exact hfC.symm
    have heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf := by
      simp only [hfe]
    rw [heq] at hmem
    exact isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)
  · have hD : 0 < S.card * e := Nat.mul_pos (Nat.pos_of_ne_zero hS0) he
    have hfh : f.IsHomogeneous (e * (r * S.card)) := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      convert this using 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨s, c, -, hc, hrel⟩ := GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh
    have hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card) := fun l => by
      rw [mul_assoc]
      exact hc l
    have hcm := fun l => aeval_mem y hy S (c l) (hc' l)
    have hF := rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm
    have hid := away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl
    have hzero := GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS
    rw [← hid] at hzero

    rw [map_add (f := _), map_sum] at hzero
    simp only [map_mul, map_pow] at hzero
    have hco := fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)
    refine ⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s,
      Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      rw [← Polynomial.mem_degreeLT]
      refine Submodule.sum_mem _ fun l hl => ?_
      rw [Polynomial.mem_degreeLT]
      refine (Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_
      exact_mod_cast Finset.mem_range.1 hl
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hzero

end GlobalTheory.CompanionTheory.GeoInteg
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_open_mem_cover_of_O1 : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := by
  first | exact @GlobalTheory.CompanionTheory.ConeWchMem.main | exact GlobalTheory.CompanionTheory.ConeWchMem.main | (intros; apply GlobalTheory.CompanionTheory.ConeWchMem.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_cup_list_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  first | exact @GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | exact GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | (intros; apply GlobalTheory.CompanionTheory.ConeRepCup.exists_rep <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatClosed

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def T (r : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (i : ℕ), r ≤ i ∧ b = f w * Lat.dpE f ξ l M i}

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, smul_smul]

theorem dpE_mem {r i : ℕ} (h : r ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ r} := by
  rw [dpE_eq, Algebra.smul_def, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_dpE (hl : l ≠ 0) (r : ℕ) : f ξ * Lat.dpE f ξ l M r =
    f ((l : W) ^ M * ((r + 1 : ℕ) : W)) * Lat.dpE f ξ l M (r + 1) := by
  have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hf : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
  have hr : ((r + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
  have key : ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r =
      (((l ^ M * (r + 1) : ℕ)) : ℚ) * (((r + 1).factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ (r + 1)) := by
    rw [Nat.factorial_succ]
    push_cast at hr ⊢
    have hu : (l : ℚ) ^ M * ((l : ℚ) ^ M)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hl')
    generalize ((l : ℚ) ^ M)⁻¹ = u at hu ⊢
    field_simp
    rw [pow_succ]
    linear_combination (-(u ^ r)) * hu
  rw [dpE_eq, dpE_eq, key, Algebra.smul_def, Algebra.smul_def, map_mul, map_natCast]
  simp only [map_mul, map_pow, map_natCast]
  push_cast
  ring

theorem T_split (r : ℕ) {b : B} (hb : b ∈ T f ξ l M r) :
    ∃ c : W, ∃ t ∈ T f ξ l M (r + 1), b = f c * Lat.dpE f ξ l M r + t := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    rcases hi.eq_or_lt with rfl | hlt
    · exact ⟨w, 0, zero_mem _, by simp⟩
    · exact ⟨0, _, AddSubgroup.subset_closure ⟨w, i, hlt, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    obtain ⟨c', t', ht', rfl⟩ := hy
    exact ⟨c + c', t + t', add_mem ht ht', by rw [map_add (f := _)]; ring⟩
  | neg x _ hx =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    exact ⟨-c, -t, neg_mem ht, by rw [map_neg]; ring⟩

theorem T_mem_span {r : ℕ} {b : B} (hb : b ∈ T f ξ l M r) : b ∈ Ideal.span {f ξ ^ r} := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M hi)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem mem_T_zero {b : B} (hb : b ∈ Lat.sub f ξ l M) : b ∈ T f ξ l M 0 := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M b).1 hb
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, Nat.zero_le _, rfl⟩

theorem xi_mul_mem (hl : l ≠ 0) (r : ℕ) (e : W) :
    f (ξ * e) * Lat.dpE f ξ l M r ∈ T f ξ l M (r + 1) := by
  refine AddSubgroup.subset_closure ⟨e * ((l : W) ^ M * ((r + 1 : ℕ) : W)), r + 1, le_rfl, ?_⟩
  rw [map_mul, map_mul f e, mul_assoc (f e), ← mul_dpE f ξ l M hl r]
  ring

variable {f ξ l M}

theorem l_ne_zero {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := fun h0 => h.l0 (by simp [h0])

theorem dvd_of_mem {m r : ℕ} (h : Lat.Hyp f ξ l m) (hr : r < m) {c : W}
    (hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)}) : ξ ∣ c := by
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (l_ne_zero h)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hc
  set s : ℚ := ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r with hs
  have hs0 : s ≠ 0 := by
    have : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
    rw [hs]; positivity
  rw [dpE_eq, ← hs] at hb
  refine h.gr r hr c (s⁻¹ • b) ?_
  have : s⁻¹ • (f c * s • f ξ ^ r) = s⁻¹ • (f ξ ^ (r + 1) * b) := by rw [hb]
  rwa [mul_smul_comm, smul_smul, inv_mul_cancel₀ hs0, one_smul, ← mul_smul_comm] at this

theorem T_of_span {m : ℕ} (h : Lat.Hyp f ξ l m) (r : ℕ) {b : B} (h0 : b ∈ T f ξ l M 0)
    (hb : b ∈ Ideal.span {f ξ ^ r}) : b ∈ T f ξ l M r := by
  induction r with
  | zero => exact h0
  | succ r ih =>
    have hr : b ∈ T f ξ l M r :=
      ih (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)) hb)
    by_cases hrm : r < m
    · obtain ⟨c, t, ht, rfl⟩ := T_split f ξ l M r hr
      have hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        have := sub_mem hb (T_mem_span f ξ l M ht)
        rwa [add_sub_cancel_right] at this
      obtain ⟨e, rfl⟩ := dvd_of_mem h hrm hc
      exact add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht
    · have hz : f ξ ^ (r + 1) = 0 := pow_eq_zero_of_le (by omega) h.nil
      rw [hz, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hb
      rw [hb]; exact zero_mem _

theorem tf_pow {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r n : ℕ)
    (a : Lat.A f ξ l M) (H : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r) :
    a ∈ pdP (Lat.γ f ξ l M hc) r := by
  induction n with
  | zero => simpa using H
  | succ n ih =>
    rw [pow_succ', mul_assoc] at H
    exact ih (GlobalTheory.T.lattice_filtration_l_torsion_free f ξ l M m h hc r _ H)

theorem lat_ι_mem_T_zero (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ T f ξ l M 0 :=
  mem_T_zero f ξ l M (Subtype.prop x)

theorem closed_succ {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r : ℕ)
    (ih : ∀ x : Lat.A f ξ l M, (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
      x ∈ pdP (Lat.γ f ξ l M hc) r)
    (x : Lat.A f ξ l M)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) (r + 1)) :
    x ∈ pdP (Lat.γ f ξ l M hc) (r + 1) := by
  have E := GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc
  have hle : pdP (Lat.γ f ξ l M hc) (r + 1) ≤ pdP (Lat.γ f ξ l M hc) r := by
    rw [E, E]
    exact Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)))
  have hxr : x ∈ pdP (Lat.γ f ξ l M hc) r := ih x fun n => sup_le_sup_left hle _ (hx n)
  have hxr' : Lat.ι f ξ l M x ∈ Ideal.span {f ξ ^ r} := by
    rw [E] at hxr; exact hxr
  by_cases hrm : r < m
  · obtain ⟨c, t, ht, hcx⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero x) hxr')
    have hz : Ideal.Quotient.mk (Ideal.span {ξ}) c = 0 := by
      refine h.cpl.toIsHausdorff.haus' _ fun n => ?_
      obtain ⟨a, y, hy, hxa⟩ := Ideal.mem_span_singleton_sup.1 (hx n)
      have hay : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r := by
        have : (l : Lat.A f ξ l M) ^ n * a = x - y := by rw [← hxa]; ring
        rw [this]; exact sub_mem hxr (hle hy)
      have ha := tf_pow h hc r n a hay
      have ha' : Lat.ι f ξ l M a ∈ Ideal.span {f ξ ^ r} := by
        rw [E] at ha; exact ha
      obtain ⟨d, t', ht', hda⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero a) ha')
      have hy' : Lat.ι f ξ l M y ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [E] at hy; exact hy
      have hxa' : Lat.ι f ξ l M a * (l : B) ^ n + Lat.ι f ξ l M y = Lat.ι f ξ l M x := by
        rw [← hxa]; simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      have e : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r =
          (l : B) ^ n * t' + Lat.ι f ξ l M y - t := by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination (-1) * hcx - hxa' + (l : B) ^ n * hda
      have hm : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [e]
        exact sub_mem (add_mem (Ideal.mul_mem_left _ _ (T_mem_span f ξ l M ht')) hy') (T_mem_span f ξ l M ht)
      have hdv := dvd_of_mem h hrm hm
      have heq : Ideal.Quotient.mk (Ideal.span {ξ}) c = Ideal.Quotient.mk (Ideal.span {ξ}) ((l : W) ^ n * d) :=
        Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hdv)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨Ideal.Quotient.mk _ d, by rw [heq, map_mul, map_pow, map_natCast]⟩
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hz)
    rw [E, Ideal.mem_comap, hcx]
    exact T_mem_span f ξ l M (add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht)
  · have h0 : f ξ ^ r = 0 := pow_eq_zero_of_le (not_lt.1 hrm) h.nil
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hxr'
    rw [E, Ideal.mem_comap, hxr']
    exact zero_mem _

theorem closed : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M),
    (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
    x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m h hc r
  induction r with
  | zero =>
    intro x _
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc 0]
    simp
  | succ r ih => exact closed_succ h hc r ih

end GlobalTheory.CompanionTheory.LatClosed
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.stable_cover_cech_vanishing : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j < s, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (HU F (St Q (Set.range U)) j))) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (𝒮 : Serre.{1} Λ) (n : ℕ),
    (∀ a b, a + b = n → 𝒮.P ((cechH F (fun α => St Q {U α}) b).cx.H a)) → 𝒮.P (HU F (St Q (Set.range U)) n)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
    {O' : Type} [CommRing O'] {R' : Type} [CommRing R'] {I' : Ideal R'} {γ' : DividedPowers I'} {p' : ℕ}
    {X' : Scheme.{0}} {q' : X' ⟶ Spec (CommRingCat.of O')} {κ' : O' →+* R' ⧸ I'}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {σ : Λ →+* Λ'}
    (G : Thick (nlFun γ' p' X' q' κ') ⥤ Thick (nlFun γ p X q κ)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module Λ (N i)] [∀ i, Module.Flat Λ (N i)]
    (F : ι → (Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ)) (F' : Thick (nlFun γ' p' X' q' κ') ⥤ ModuleCat.{0} Λ')
    (τ : ∀ i, N i → ∀ T, (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : Λ) n T x, τ i (r • n) T x = σ r • τ i n T x)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p' X' q' κ')))
    {A : Type} [Fintype A] (U : A → X.Opens) (U' : A → X'.Opens) (h : ∀ α T, St Q' {U' α} T → St Q {U α} (G.obj T))
    (hS : ∀ (S : Finset A) T, St Q' {⨅ α ∈ S, U' α} T → St Q {⨅ α ∈ S, U α} (G.obj T))
    (hR : ∀ T, St Q' (Set.range U') T → St Q (Set.range U) (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q {⨅ α ∈ S, U α}) j)
      (M' := HU F' (St Q' {⨅ α ∈ S, U' α}) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (hS S)).pull j x) →
    ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q (Set.range U)) j) (M' := HU F' (St Q' (Set.range U')) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hR).pull j x) := by
  first | exact @GlobalTheory.CompanionTheory.GlobSt.glob_st | exact GlobalTheory.CompanionTheory.GlobSt.glob_st | (intros; apply GlobalTheory.CompanionTheory.GlobSt.glob_st <;> assumption)
end
