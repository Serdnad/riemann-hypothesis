module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem linTrace_eq_neg_nextCoeff {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : Module.End F W) :
    LinearMap.trace F W g = -g.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_vmap {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (A : AbVar K)
    [Module.Finite ℚ_[l] (Vl l A)] (f : End A) :
    (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly := by
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _)
    (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
    (fun n => by
      rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
      simp)
  rw [← key, Polynomial.map_map]
  congr 1

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem charpoly_tate_det_trace :
    ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
      (∀ [Module.Finite ℚ_[l] (Vl l A)],
        (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly) ∧
      (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)],
        (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧
      LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) ∧
      LinearMap.trace ℚ_[l] _ (vmap l f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  refine ⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
    rw [hc]
    exact charpoly_map_vmap l hl A f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      have h : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := A)) f
      simp only [h, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp

end GlobalTheory.AV.AbVar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.PerBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem eq_zero_of_sum_eq_zero (hpq : ¬ 1 ≤ Dw.p + Dw.q) (T : UTrait Xo c) (x : T.P.D.toPre.X) : x = 0 := by
  have hr := UTrait.finrank_le_min E H Dw l Xo c T
  have h0 : Module.finrank (𝓞 E) T.P.D.toPre.X = 0 := by omega
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 x
  obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have h : n • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hax, smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

end GlobalTheory.UPoinc.PerBound


open GlobalTheory.UPoinc.PerBound in
theorem GlobalTheory.UPoinc.lam_of_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ p _ z₁ hz
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · exact ⟨0, fun t x hx => absurd (eq_zero_of_sum_eq_zero hpq t.T x) hx⟩
  obtain ⟨m, X', U, hU, hcov⟩ := GlobalTheory.T.exists_finite_regular_thetaSetup_cover E H Dw l Xo c C (GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint E H Dw hpq l Xo c C)
  choose K hK using fun k => GlobalTheory.T.unitary_classical_trait_periods_bounded_below E H Dw l Xo c C (X' k) p
  choose e he1 he using fun k => GlobalTheory.T.exists_pow_norm_val_le_unitaryTheta_finite_models E H Dw l Xo c C X₁ (X' k) z₁
  refine ⟨∑ k, (e k : ℝ) * |K k|, fun t x hx => ?_⟩
  have hzc : IsClosed ({X₁.π z₁} : Set C.Z) := by
    haveI := X₁.fin
    have := X₁.π.isClosedMap _ hz
    rwa [Set.image_singleton] at this
  obtain ⟨k, w, hwU, hw⟩ := hcov ((spMap t.ι ≫ t.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)))
  have hgen : (X' k).π w = (gPt p ≫ (t.y ≫ X₁.π)) (IsLocalRing.closedPoint (PadicAlgCl p)) := by
    rw [hw, t.comm]
    rfl
  obtain ⟨y', hy'π, hy'w⟩ := GlobalTheory.T.exists_padicTrait_lift_finite_through_point _ _ (X' k).π (X' k).fin p (t.y ≫ X₁.π) w hgen
  have hz'π : (X' k).π (y' (cPt p)) = X₁.π z₁ := by
    have := congrArg (fun f => f (cPt p)) hy'π
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, t.cen]
  have hz'c := GlobalTheory.T.isClosed_singleton_of_isFinite_of_isClosed_image _ _ _ (X' k).fin (y' (cPt p)) (hz'π ▸ hzc)
  let t' : UCTrait (X' k) p (y' (cPt p)) :=
    { y := y', cen := rfl, T := t.T, ι := t.ι, int := t.int, comm := by rw [hy'π]; exact t.comm }
  have hreg : (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ t'.y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    show (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ y') (IsLocalRing.closedPoint (PadicAlgCl p)))
    rw [hy'w]
    exact (hU k).trans (RatModel.ringOn_le_O hwU)
  obtain ⟨h', hh'm, hh'⟩ := hK k (y' (cPt p)) hz'c t' hreg x hx
  obtain ⟨h, hhm, hh⟩ := he k p t (y' (cPt p)) t' hy'π.symm h' hh'm
  refine ⟨h, hhm, le_trans ?_ hh⟩
  have hs : 0 ≤ t.sc * t.T.be x x := mul_nonneg (sc_pos t).le (by exact_mod_cast (be_pos _ x hx).le)
  have hsum : (e k : ℝ) * |K k| ≤ ∑ k, (e k : ℝ) * |K k| :=
    Finset.single_le_sum (f := fun k => (e k : ℝ) * |K k|) (fun k _ => by positivity) (Finset.mem_univ k)
  have hKk : (e k : ℝ) * K k ≤ (e k : ℝ) * |K k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  calc Real.exp (-((∑ k, (e k : ℝ) * |K k|) * (t.sc * t.T.be x x)))
      ≤ Real.exp (-(K k * (t.sc * t.T.be x x))) ^ e k := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ ‖t'.val h'‖ ^ e k := pow_le_pow_left₀ (Real.exp_pos _).le hh' _
end

section

open GlobalTheory.EtC

namespace GlobalTheory.QPic

theorem pic0 : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := GlobalTheory.T.pic_eq_one_of_forall_prime_maximal

theorem incomp : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := GlobalTheory.T.ind_etale_prime_comparison

theorem poly : ∀ (T : Type) [CommRing T] [IsDomain T] (P P' : Ideal (Polynomial T)), P.IsPrime → P'.IsPrime → P ≤ P' → P ≠ ⊥ → P'.comap (algebraMap T (Polynomial T)) = ⊥ → P = P' := by
  intro T _ _ P P' hP hP' hle h0 hC
  let K := FractionRing T
  letI : Algebra (Polynomial T) (Polynomial K) := Polynomial.algebra T K
  haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors T)) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors T) K
  set M := Submonoid.map Polynomial.C (nonZeroDivisors T) with hM
  have hdisj' : Disjoint (M : Set (Polynomial T)) (P' : Set (Polynomial T)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    have : s ∈ P'.comap (algebraMap T (Polynomial T)) := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hsP
    rw [hC, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hs this
  have hdisj : Disjoint (M : Set (Polynomial T)) (P : Set (Polynomial T)) :=
    hdisj'.mono_right hle
  have hPK := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P hP hdisj
  have hP'K := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P' hP' hdisj'
  have hc := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP hdisj
  have hc' := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP' hdisj'
  have hM0 : (0 : Polynomial T) ∉ M := by
    intro h
    obtain ⟨s, hs, hs0⟩ := Submonoid.mem_map.mp h
    exact nonZeroDivisors.ne_zero hs (Polynomial.C_eq_zero.mp hs0)
  have hne : P.map (algebraMap (Polynomial T) (Polynomial K)) ≠ ⊥ := by
    intro hb
    apply h0
    rw [← hc, hb, eq_bot_iff]
    intro x hx0
    have hx : algebraMap (Polynomial T) (Polynomial K) x = 0 := (Ideal.mem_bot).mp hx0
    exact (Ideal.mem_bot).mpr (IsLocalization.injective (Polynomial K) (le_nonZeroDivisors_of_noZeroDivisors hM0)
      (hx.trans (map_zero _).symm))
  have hmax : (P.map (algebraMap (Polynomial T) (Polynomial K))).IsMaximal := hPK.isMaximal hne
  have heq := hmax.eq_of_le hP'K.ne_top (Ideal.map_mono hle)
  rw [← hc, ← hc', heq]

theorem pic_transfer {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (q : ℕ)
    (h : ∀ c : CommRing.Pic S, c ^ q = 1 → c = 1) (c : CommRing.Pic R) (hc : c ^ q = 1) : c = 1 := by
  have h1 : CommRing.Pic.mapRingHom e.toRingHom c = 1 := h _ (by rw [← map_pow, hc, map_one])
  have h2 : CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom c) = c := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]
  rw [← h2, h1, map_one]

theorem primes_eq (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (hind : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i))
    (p p' : Ideal O) [p.IsPrime] [p'.IsPrime] (hle : p ≤ p') (h0 : p ≠ ⊥)
    (hT : p'.comap (algebraMap T O) = ⊥) : p = p' := by
  have hinc := incomp (Polynomial T) O hind
  refine hinc p p' inferInstance inferInstance hle ?_
  refine poly T _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (Ideal.comap_mono hle) ?_ ?_
  · intro hb
    have : (⊥ : Ideal O).comap (algebraMap (Polynomial T) O) = p.comap (algebraMap (Polynomial T) O) := by
      apply le_antisymm (Ideal.comap_mono bot_le); rw [hb]; exact bot_le
    exact h0 (hinc ⊥ p Ideal.isPrime_bot inferInstance bot_le this).symm
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hT

end GlobalTheory.QPic


open GlobalTheory.QPic in
theorem GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ c hc
  haveI : IsIntegrallyClosed T := GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hAIC
  haveI : IsDomain O := (GlobalTheory.indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind).1
  let eA := Localization.tensorRightAlgEquiv (nonZeroDivisors T) A
  by_cases hI : RingHom.ker (π : O →+* A) = ⊥
  · have hinj : Function.Injective π := (RingHom.injective_iff_ker_eq_bot _).mpr hI
    let eπ : O ≃ₐ[T] A := AlgEquiv.ofBijective (π.restrictScalars T) ⟨hinj, hπ⟩
    let e1 : TensorProduct T (FractionRing T) A ≃ₐ[T] TensorProduct T (FractionRing T) O :=
      Algebra.TensorProduct.congr AlgEquiv.refl eπ.symm
    let e2 := Localization.tensorRightAlgEquiv (nonZeroDivisors T) O
    refine pic_transfer (e1.toRingEquiv.trans e2.toRingEquiv) q ?_ c hc
    exact GlobalTheory.pic_localization_strictHenselisation_no_torsion T O q ⟨inferInstance, hAIC⟩ hq
      (Nat.pos_of_ne_zero (NeZero.ne q)) hind
  · refine pic_transfer eA.toRingEquiv q (fun c' _ => pic0 _ ?_ c') c hc
    intro Q hQ
    obtain ⟨Q', hQ'max, hle⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    suffices hQQ : Q = Q' by rw [hQQ]; exact hQ'max
    set L := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
    have hQ'p : Q'.IsPrime := hQ'max.isPrime
    set p := (Q.comap (algebraMap A L)).comap (π : O →+* A) with hpdef
    set p' := (Q'.comap (algebraMap A L)).comap (π : O →+* A) with hp'def
    have hpp : p = p' := by
      refine primes_eq T O hind p p' (Ideal.comap_mono (Ideal.comap_mono hle)) ?_ ?_
      · intro hb
        apply hI
        rw [eq_bot_iff, ← hb]
        intro x hx
        rw [RingHom.mem_ker] at hx
        simp [hpdef, hx]
      · rw [eq_bot_iff]
        intro t ht
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap] at ht
        rw [Ideal.mem_bot]
        by_contra ht0
        have hcomm : (π : O →+* A) (algebraMap T O t) = algebraMap T A t := by
          rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, IsScalarTower.algebraMap_apply T (Polynomial T) A]
          exact π.commutes _
        rw [hcomm] at ht
        have hu : IsUnit (algebraMap A L (algebraMap T A t)) :=
          IsLocalization.map_units L (⟨algebraMap T A t, t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩ :
            Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
        exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ ht hu)
    have hqq : Q.comap (algebraMap A L) = Q'.comap (algebraMap A L) := by
      rw [← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q.comap (algebraMap A L)),
        ← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q'.comap (algebraMap A L))]
      exact congrArg _ hpp
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q,
      ← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q']
    exact congrArg (Ideal.map (algebraMap A L)) hqq
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

namespace GlobalTheory.HeatPts

theorem exists_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ h12 y
  have hw : (spMap ρ ≫ (P.D.toPre.c y).left) ≫ P.D.toPre.P.A.hom = 𝟙 _ ≫ spMap ρ := by
    rw [Category.assoc, Over.w]; simp
  refine ⟨h₁.1.lift (spMap ρ ≫ (P.D.toPre.c y).left) (𝟙 _) hw, h₁.1.lift_snd _ _ _, h₁.1.lift_fst _ _ _, ?_⟩
  exact GlobalTheory.T.translation_horizontal_of_commuting_heatOperators E H k m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' inferInstance π₁ π₂ h₁ h₂ h12 y _
    (h₁.1.lift_snd _ _ _) (h₁.1.lift_fst _ _ _)

end GlobalTheory.HeatPts
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

theorem _root_.GlobalTheory.T.unitPart_periods_constant_along_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  first | exact @GlobalTheory.UnitsAlong.unitTau_along | exact GlobalTheory.UnitsAlong.unitTau_along | (intros; apply GlobalTheory.UnitsAlong.unitTau_along <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.memberTerms_isThetaTerms_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  first | exact @GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms | exact GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms | (intros; apply GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_member_terms_integral_unit_shift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * mono W t δ mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_terms | exact GlobalTheory.Poinc.IntTerm.exists_terms | (intros; apply GlobalTheory.Poinc.IntTerm.exists_terms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twistWeight_wellDefined_on_lattice_class : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : (Fin 8 → Y1) → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.Poinc.Sep.WtWd.wt_wd | exact GlobalTheory.Poinc.Sep.WtWd.wt_wd | (intros; apply GlobalTheory.Poinc.Sep.WtWd.wt_wd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime : ∀ (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left), Vert (σ.C x).G.hom (σ.ρ x σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C x).G.hom) ((σ.C x).G.hom z).asIdeal (σ.θ x) (σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z))) (regSet z) ∧ (σ.θ x) ⁻¹' (regSet z) = σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z)) := by
  first | exact @GlobalTheory.Desc.GaussPt.gaussAt_vert | exact GlobalTheory.Desc.GaussPt.gaussAt_vert | (intros; apply GlobalTheory.Desc.GaussPt.gaussAt_vert <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localSection_thetaQuotient_projChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  first | exact @GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | exact GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | (intros; apply GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∃ P₀ : LB (G2 A').left, P₀.IsLB ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (exact GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient <;> assumption)
end
