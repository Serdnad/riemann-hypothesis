module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle429
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithful
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.WachMat

section Series

open PowerSeries

variable {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem constantCoeff_rescale' (u : L) (f : L⟦X⟧) : constantCoeff (rescale u f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]

theorem X_pow_dvd_rescale (u : L) (f : L⟦X⟧) (a : ℕ) (h : X ^ a ∣ f) : X ^ a ∣ rescale u f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_rescale, h m hm, mul_zero]

theorem map_constantCoeff_eq_one (G : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) :
    G.map (constantCoeff (R := L)) = 1 := by
  ext i j
  have := X_dvd_iff.1 (hG i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem X_pow_dvd_of_rescale (u : L) (hu0 : u ≠ 0) (hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1) (w : L⟦X⟧) (hw : IsUnit w)
    (a : ℕ) (B G G₁ : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) (hG₁ : ∀ i j, X ∣ (G₁ - 1) i j)
    (h : (X * w) ^ a • (G * B.map (rescale u)) = (rescale u (X * w)) ^ a • (B * G₁)) :
    ∀ i j, X ^ a ∣ B i j := by
  have key : ∀ k, k ≤ a → ∀ i j, X ^ k ∣ B i j := by
    intro k
    induction k with
    | zero => intro _ i j; simp
    | succ k ih =>
      intro hk i j
      choose B' hB' using ih (by omega)
      have hB : B = (X : L⟦X⟧) ^ k • Matrix.of B' := by
        ext1 i j; rw [hB']; rfl
      have hBu : B.map (rescale u) = ((C u) ^ k * (X : L⟦X⟧) ^ k) • (Matrix.of B').map (rescale u) := by
        ext1 i j
        rw [Matrix.map_apply, hB', map_mul, map_pow, rescale_X, mul_pow]; rfl
      rw [hBu] at h
      rw [hB] at h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, rescale_X] at h
      have h1 := congrFun (congrFun h i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at h1
      have h2 : w ^ a * C u ^ k * (G * (Matrix.of B').map (rescale u)) i j
          = C u ^ a * rescale u w ^ a * (Matrix.of B' * G₁) i j := by
        apply mul_left_cancel₀ (pow_ne_zero (a + k) (X_ne_zero (R := L)))
        linear_combination h1
      have h3 := congrArg (constantCoeff (R := L)) h2
      have e1 : constantCoeff ((G * (Matrix.of B').map (rescale u)) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G hG,
          Matrix.one_mul, Matrix.map_apply, Matrix.map_apply, constantCoeff_rescale']
        rfl
      have e2 : constantCoeff ((Matrix.of B' * G₁) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G₁ hG₁,
          Matrix.mul_one, Matrix.map_apply]
        rfl
      simp only [map_mul, map_pow, constantCoeff_C, constantCoeff_rescale', e1, e2] at h3
      have hw0 : constantCoeff w ≠ 0 := (isUnit_iff_constantCoeff.1 hw).ne_zero
      obtain ⟨d, rfl⟩ : ∃ d, a = k + (d + 1) := ⟨a - (k + 1), by omega⟩
      have h4 : (constantCoeff w ^ (k + (d + 1)) * u ^ k * (u ^ (d + 1) - 1)) * constantCoeff (B' i j) = 0 := by
        linear_combination -h3
      have h5 : constantCoeff (B' i j) = 0 :=
        (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hu0))
          (sub_ne_zero.2 (hu _ (by omega))))
      rw [hB', pow_succ]
      exact mul_dvd_mul_left _ (X_dvd_iff.2 h5)
  exact key a le_rfl

end Series

theorem pow_smul_eq {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (Q : R) (m m' : ℕ)
    (B B' Pm P₁ P₁' : Matrix ι ι R) (h1 : P₁ * P₁' = (Q ^ m') • (1 : Matrix ι ι R))
    (h2 : Pm * B' = (Q ^ m) • (B * P₁)) : Q ^ (m + m') • B = Pm * B' * P₁' := by
  rw [h2, Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_add]

theorem dvd_map_of_pow_smul_eq {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : R)
    (hQ : IsUnit (f Q)) (m : ℕ) (B B' Pm P₁' : Matrix ι ι R) (h : Q ^ m • B = Pm * B' * P₁') (x : S)
    (hx : ∀ i j, x ∣ f (B' i j)) (i j : ι) : x ∣ f (B i j) := by
  have h1 := congrArg f (congrFun (congrFun h i) j)
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow] at h1

  rw [← (hQ.pow m).dvd_mul_left, h1, Matrix.mul_apply, map_sum]
  refine Finset.dvd_sum fun k _ => ?_

  rw [map_mul, Matrix.mul_apply, map_sum]
  refine Dvd.dvd.mul_right (Finset.dvd_sum fun k' _ => ?_) _
  rw [map_mul]
  exact (hx _ _).mul_left _



theorem X_pow_dvd_entry : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (r a m m' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r) (Fin r) (AA K LL)), (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) → P₁ * P₁' = (W.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (AA K LL)) → Pm * B.map W.φA = (W.Q ^ m) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j := by
  intro D HW l hl K s LL h W r a m m' B G G₁ Pm P₁ P₁' hG hG₁ hγ hP hφ
  obtain ⟨Lγ, Lφ⟩ : LevLaws W := GlobalTheory.NL.Expansion.levLaws D HW l K s LL h
  have Lp := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h
  obtain ⟨χ, hχ, -, -, -, -, hgam, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨-, Wd, -⟩ := GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at Lγ Lφ
  have hroot : ∀ (j : ℕ) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    intro j ζ h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩
  set u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) with hudef
  have hu0 : u ≠ 0 := ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1 := by
    intro n hn h1
    have h2 := GlobalTheory.Cyc.norm_unit_zpow_sub_one l s (χ W.gam) h.1 h.2.1 hgam n (by exact_mod_cast hn)
    have h3 : ((χ W.gam : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1 := by
      have inj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
        rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
        exact (algebraMap ℚ_[l] ↥LL.1).injective.comp Subtype.val_injective
      apply inj
      rw [map_pow, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]
      exact h1
    rw [zpow_natCast, Units.val_pow_eq_pow_val, h3, sub_self, norm_zero] at h2
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    refine mul_ne_zero (zpow_pos hl0 _).ne' (norm_ne_zero_iff.2 ?_) h2.symm
    exact_mod_cast hn
  have base : ∀ (i : Let K) p q, PowerSeries.X ^ a ∣ W.lev i 1 (B p q) := by
    intro i
    have r1 : IsPrimitiveRoot (1 : ↥LL.1) (l ^ 0) := by
      rw [pow_zero]; exact IsPrimitiveRoot.one
    obtain ⟨⟨x, -, hx, w₀, -, hπ⟩, -, hX, -⟩ := Lp i 1 ⟨0, r1⟩
    obtain ⟨⟨w, hw, hX⟩, -⟩ := hX (one_pow _)
    rw [hx, sub_self, map_zero, zero_add] at hπ
    have hγ1 : ∀ f, W.lev i 1 (W.γA W.gam f) = PowerSeries.rescale u (W.lev i 1 f) := by
      refine Lγ W.gam i 1 1 0 1 r1 ?_ (one_pow _).symm
      rw [Nat.cast_one, W.gam_gen]
      exact_mod_cast Nat.zero_le _
    have hone : ∀ G : Matrix (Fin r) (Fin r) (AA K LL), (∀ p q, (G - 1) p q ∈ Ideal.span {(letπ : AA K LL)}) →
        ∀ p q, PowerSeries.X ∣ (G.map (W.lev i 1) - 1) p q := by
      intro G hG p q
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hG p q)
      have e : (G.map (W.lev i 1) - 1) p q = W.lev i 1 ((G - 1) p q) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e, hc, map_mul, hπ, mul_assoc]
      exact dvd_mul_right _ _
    refine X_pow_dvd_of_rescale u hu0 hu w hw a (B.map (W.lev i 1)) (G.map (W.lev i 1)) (G₁.map (W.lev i 1))
      (hone G hG) (hone G₁ hG₁) ?_
    ext1 p q
    have h1 := congrArg (W.lev i 1) (congrFun (congrFun hγ p) q)

    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum,
    hγ1] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ← hX]
    exact h1
  have hB := pow_smul_eq W.Q m m' B (B.map W.φA) Pm P₁ P₁' hP hφ
  have step : ∀ j : ℕ, j ≤ s - 1 → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∀ p q,
      PowerSeries.X ^ a ∣ W.lev i ζ (B p q) := by
    intro j
    induction j with
    | zero =>
      intro _ i ζ hζ
      rw [pow_zero, pow_one] at hζ
      subst hζ
      exact base i
    | succ j ih =>
      intro hj i ζ hζ
      have hr := hroot _ ζ hζ
      have hζ' : ζ ^ (l ^ (s - 1)) = 1 := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
        rw [hd, pow_add, pow_mul, hζ, one_pow]
      obtain ⟨-, -, hX, -⟩ := Lp i ζ hr
      obtain ⟨-, hQ⟩ := hX hζ'
      refine dvd_map_of_pow_smul_eq (W.lev i ζ : AA K LL →+* PowerSeries ↥LL.1) W.Q hQ _ B _ Pm P₁' hB _ fun p q => ?_
      change _ ∣ W.lev i ζ (W.φA (B p q))
      rw [Lφ i ζ hr]
      refine X_pow_dvd_rescale _ _ _ (ih (by omega) _ _ ?_ p q)
      rw [← pow_mul, ← pow_succ', hζ]
  intro p q
  refine Wd a (B p q) fun i ζ hζ => ?_
  exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 (step _ le_rfl i ζ hζ p q))

end GlobalTheory.NL.WachMat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.etaleRing_free_over_frobenius_image : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ x : W.EE, ∃! c : Fin l → W.EE, x = ∑ j : Fin l, algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ (j : ℕ) * W.φE (c j) := by
  first | exact @GlobalTheory.NL.FreeEE.ee_free | exact GlobalTheory.NL.FreeEE.ee_free | (intros; apply GlobalTheory.NL.FreeEE.ee_free <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.wachFunctor_fullyFaithful : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : W.DD T →ₗ[W.EE] W.DD T'), (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) → ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  first | exact @GlobalTheory.FontaineFullyFaithful.main | exact GlobalTheory.FontaineFullyFaithful.main | (intros; apply GlobalTheory.FontaineFullyFaithful.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BaseChangeExistsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Matrix

section Definite

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_hD (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x : S.V) :
    τ (S.hD x x) = star (fun a => τ (S.frame.repr x a)) ⬝ᵥ
      (S.gram.map τ *ᵥ fun a => τ (S.frame.repr x a)) := by
  rw [HSpace.hD, hT_expand]

  simp only [map_sum, map_mul, hτ, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply,
  mul_assoc]
  rfl

theorem denseRange_emb [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure τ.fieldRange) with h | h
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : τ x ∈ τ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    simp
  · have : closure (Set.range τ) = Set.univ := congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h
    exact dense_iff_closure_eq.2 this

theorem closed_of_coords [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (τ : E →+* ℂ) {C : Set (Fin S.rank → ℂ)}
    (hC : IsClosed C) (h : ∀ x : S.V, (fun a => τ (S.frame.repr x a)) ∈ C) (y : Fin S.rank → ℂ) : y ∈ C := by
  have hd : DenseRange (Pi.map fun (_ : Fin S.rank) => (τ : E → ℂ)) :=
    DenseRange.piMap fun _ => denseRange_emb τ
  refine hd.induction_on y hC fun v => ?_
  have := h (S.frame.equivFun.symm v)
  have e : (fun a => τ (S.frame.repr (S.frame.equivFun.symm v) a)) =
      Pi.map (fun (_ : Fin S.rank) => (τ : E → ℂ)) v := by
    funext a
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  rwa [e] at this

theorem coords_ne_zero (S : HSpace E) (τ : E →+* ℂ) {x : S.V} (hx : x ≠ 0) :
    (fun a => τ (S.frame.repr x a)) ≠ 0 := by
  intro h
  apply hx
  rw [← S.frame.repr.map_eq_zero_iff]
  ext a
  simpa using congrFun h a

theorem continuous_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun y : Fin n → ℂ => (star y ⬝ᵥ (M *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem sig_pos_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (S.rank, 0) ↔ ∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_pos _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, 0 ≤ (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re := fun y =>
      closed_of_coords S τ (isClosed_le continuous_const (continuous_quad (S.gram.map τ))) (fun x => by
        show (0 : ℝ) ≤ _
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hq : (S.sig τ).2 = 0 := by
      by_contra hq
      have h1 := hall (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext (by simp only; omega) hq

theorem sig_neg_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (0, S.rank) ↔ ∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0 := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_neg _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re ≤ 0 := fun y =>
      closed_of_coords S τ (isClosed_le (continuous_quad (S.gram.map τ)) continuous_const) (fun x => by
        show _ ≤ (0 : ℝ)
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hp : (S.sig τ).1 = 0 := by
      by_contra hp
      have h1 := hall (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext hp (by simp only; omega)

end Definite

theorem unram_of_cm (D : D7) (hc : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _) (w : PlE D.host) :
    Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 hU ⟨w.asIdeal, w.isPrime⟩

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

end Concl

end GlobalTheory.BaseChangeExistsCompare

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet : ∀ (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : PlE D.host),
    (∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0) → placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)) →
    (∀ Q ∈ Sb, Q ∈ S0) → IsSplitPl D.host P → P ∉ S0 →
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  first | exact @GlobalTheory.ConjPlaceOff.exists_conj_off | exact GlobalTheory.ConjPlaceOff.exists_conj_off | (intros; apply GlobalTheory.ConjPlaceOff.exists_conj_off <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.invariants_statement_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.H0InvariantsTheorem D HW F := by
  first | exact @GlobalTheory.invariants_of_field_of_norms | exact GlobalTheory.invariants_of_field_of_norms | (intros; apply GlobalTheory.invariants_of_field_of_norms <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  first | exact @GlobalTheory.AmbBlockDecomp.main | exact GlobalTheory.AmbBlockDecomp.main | (intros; apply GlobalTheory.AmbBlockDecomp.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue : ∀ (D : D7) (C : NChoice D), NChTie D C → ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤ BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (KillingConditions.psiW C (D.nd.w i)) (D.nd.plOm.1 v) := by
  first | exact @GlobalTheory.CondTieChoice.conductor_le_tameVal | exact GlobalTheory.CondTieChoice.conductor_le_tameVal | (intros; apply GlobalTheory.CondTieChoice.conductor_le_tameVal <;> assumption)
end
