module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem UpperTheory.Gal.G1.exists_local (hF : LocFour) (hU : LocUnit) (hR : LocRoot) (hS : SplitRep)
    (F : Type) [Field F] [NumberField F] (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm ≠ 0) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f : Fin 4 → v.adicCompletion F,
      algebraMap F (v.adicCompletion F) (c : F) * (qf tr nm (f 0) (f 1) + qf tr nm (f 2) (f 3)) = 1 ∧
      (c ∉ v.asIdeal → (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) → ∀ i, f i ∈ v.adicCompletionIntegers F) := by
  have hcF : (c : F) ≠ 0 := by simpa using hc
  have hcv : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    simpa using hcF
  by_cases hg : c ∉ v.asIdeal ∧ (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm)
  · obtain ⟨hcm, hor⟩ := hg
    have hval : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)).trans ?_
      have h0 : v.valuation F (c : F) = v.intValuation c := HeightOneSpectrum.valuation_of_algebraMap v c
      rw [h0]
      first
        | exact (HeightOneSpectrum.intValuation_eq_one_iff v).2 hcm
        | exact le_antisymm (v.intValuation_le_one c)
            (not_lt.1 fun h => hcm ((v.intValuation_lt_one_iff_mem c).1 h))
    have hval' : Valued.v (algebraMap F (v.adicCompletion F) (c : F))⁻¹ = 1 := by
      rw [map_inv₀, hval, inv_one]
    let c1 : v.adicCompletionIntegers F := ⟨_, hval.le⟩
    let c2 : v.adicCompletionIntegers F := ⟨_, hval'.le⟩
    have h12 : c2 * c1 = 1 := Subtype.ext (inv_mul_cancel₀ hcv)
    have hu : IsUnit c2 := isUnit_iff_exists_inv.2 ⟨c1, h12⟩
    obtain ⟨a, b, hab⟩ : ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = c2 := by
      rcases hor with h | ⟨q, hq, hqv, hqd, hr⟩
      · exact hU F v tr nm h c2 hu
      · obtain ⟨ρ, h1, h2⟩ := hR F v tr nm q hq hqv hqd hr
        exact hS _ tr nm ρ h1 h2 c2
    have hab' : qf tr nm (a : v.adicCompletion F) (b : v.adicCompletion F)
        = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := by
      have := congrArg (Subtype.val) hab
      simpa [qf] using this
    refine ⟨![a, b, 0, 0], ?_, fun _ _ i => ?_⟩
    · simp only [Matrix.cons_val]
      have h0 : qf tr nm (0 : v.adicCompletion F) 0 = 0 := by simp [qf]
      rw [hab', h0, add_zero, mul_inv_cancel₀ hcv]
    · fin_cases i
      · exact a.2
      · exact b.2
      · exact zero_mem _
      · exact zero_mem _
  · obtain ⟨a, b, a', b', h⟩ := hF F v tr nm hd _ (inv_ne_zero hcv)
    refine ⟨![a, b, a', b'], ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
    simp only [Matrix.cons_val]
    rw [h, mul_inv_cancel₀ hcv]

theorem UpperTheory.Gal.G1.pAdFour :
    LocFour → LocUnit → LocRoot → SplitRep → AdFour := by
  intro hF hU hR hS F _ _ tr nm hd c hc
  choose f hf1 hf2 using exists_local hF hU hR hS F tr nm hd c hc
  have hD : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ≠ 0 := by
    have : (2 * (tr ^ 2 - 4 * nm) : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hd
    exact_mod_cast this
  have hI : Ideal.span {((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hD hc
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hev : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, f v i ∈ v.adicCompletionIntegers F := by
    intro i
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    have h1 : c ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_left _ _ hm)
    have h2 : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_right _ _ hm)
    exact hv (hf2 v h1 (Or.inl h2) i)
  let A : Fin 4 → FiniteAdeleRing (𝓞 F) F := fun i => ⟨fun v => f v i, hev i⟩
  refine ⟨A, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have := hf1 v
    let φ : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      { toFun := fun x => x v
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have key : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) *
        (qf tr nm (A 0) (A 1) + qf tr nm (A 2) (A 3))) = φ 1 := by
      simp only [qf, map_mul, map_add (f := _), map_pow, map_intCast, map_one]
      have hA : ∀ i, φ (A i) = f v i := fun _ => rfl
      have hc' : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F)) =
          algebraMap F (v.adicCompletion F) (c : F) := rfl
      rw [hc']
      simp only [hA]
      simpa only [qf] using this
    exact key
  · intro v q hq hqv hqd hr hcv i
    exact hf2 v hcv (Or.inr ⟨q, hq, hqv, hqd, hr⟩) i
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pUnitCls :
    Scale → ZUnitNorm → ZSqFin → UnitCls := by
  intro hScale hNorm hSq p D hD
  choose sc hsc0 hsc using hScale p
  choose m κ hκ using hSq
  have hfin : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 * D : ℤ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      omega
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  haveI : Finite {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal} := hfin.to_subtype
  refine ⟨(v : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}) → Option (Fin (m v.1)),
    inferInstance, fun t v => if h : (v.1 : HeightOneSpectrum ℤ).asIdeal ≠ Ideal.span {(p : ℤ)}
      then some (κ v.1 (AfP.eval (⟨v.1, h⟩ : AwayP p) (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t)))
      else none, ?_⟩
  intro t t' hk
  refine ⟨sc t' / sc t, div_pos (hsc0 t') (hsc0 t), fun v => ?_⟩
  have hunit : ∀ r : (AfP p)ˣ, AfP.eval v (r : AfP p) ≠ 0 := by
    intro r
    have h1 : AfP.eval v (r : AfP p) * AfP.eval v ((r⁻¹ : (AfP p)ˣ) : AfP p) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hsne : ∀ r : (AfP p)ˣ,
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r) ≠ 0 :=
    fun r => (map_ne_zero _).2 (hsc0 r).ne'
  have hval : ∀ r : (AfP p)ˣ, Valued.v (AfP.eval v (r : AfP p) /
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r)) = 1 := by
    intro r
    rw [map_div₀, hsc r v, div_self]
    exact (Valuation.ne_zero_iff _).2 (hsne r)
  suffices hs : ∃ x y : HeightOneSpectrum.adicCompletion ℚ v.1,
      AfP.eval v (t' : AfP p) / algebraMap ℚ _ (sc t') =
        AfP.eval v (t : AfP p) / algebraMap ℚ _ (sc t) * (x ^ 2 - (D : _) * y ^ 2) by
    obtain ⟨x, y, hxy⟩ := hs
    refine ⟨x, y, ?_⟩
    rw [map_div₀]
    have e := hsne t
    have e' := hsne t'
    rw [div_eq_iff e'] at hxy
    rw [hxy]
    field_simp
  by_cases h2 : (2 * D : ℤ) ∈ v.1.asIdeal
  · have hk' := congrFun hk ⟨v.1, h2⟩
    dsimp only at hk'
    rw [dite_eq_left v.2, dite_eq_left v.2] at hk'
    have hk'' := Option.some.inj hk'
    obtain ⟨z, hz⟩ := hκ v.1 _ _ (hval t) (hval t') hk''
    refine ⟨z, 0, ?_⟩
    rw [hz]
    ring
  · have hne : AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t) ≠ 0 :=
      div_ne_zero (hunit t) (hsne t)
    have hv1 : Valued.v ((AfP.eval v (t' : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t')) /
        (AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t))) = 1 := by
      rw [map_div₀, hval t, hval t', div_one]
    obtain ⟨x, y, hxy⟩ := hNorm v.1 D h2 _ hv1
    refine ⟨x, y, ?_⟩
    rw [← hxy, mul_div_assoc', mul_div_cancel_left₀ _ hne]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma unit_add_nonunit {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (hx : IsUnit x) (hy : ¬ IsUnit y) : IsUnit (x + y) := by
  by_contra h
  have hy' : ¬ IsUnit (-y) := by rwa [IsUnit.neg_iff]
  have := IsLocalRing.nonunits_add h hy'
  rw [add_neg_cancel_right] at this
  exact this hx

private lemma natCast_not_isUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∈ v.asIdeal) :
    ¬ IsUnit (q : v.adicCompletionIntegers F) := by
  intro hu
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
  have h1 : v.intValuation (q : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hq
  have h2 : ((q : v.adicCompletionIntegers F) : v.adicCompletion F) = (q : v.adicCompletion F) := by
    simp
  have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  have h4 := HeightOneSpectrum.valuation_of_algebraMap (K := F) v (q : 𝓞 F)
  push_cast at h3 h4
  rw [h2, h3, h4] at hu
  exact (ne_of_lt h1) hu

theorem UpperTheory.Gal.G1.pLocRoot :
    HenselV → LocRoot := by
  intro hH F _ _ v tr nm q hqp hqv hdisc hr
  obtain ⟨r, k, hk⟩ := hr
  have hq : ¬ IsUnit (q : v.adicCompletionIntegers F) := natCast_not_isUnit F v q hqv
  have hqi : Irreducible (q : ℤ) := (Nat.prime_iff_prime_int.mp hqp).irreducible
  have hint : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → IsUnit (n : v.adicCompletionIntegers F) := by
    intro n hn
    obtain ⟨a, b, hab⟩ := (hqi.coprime_iff_not_dvd).2 hn
    have hab' : ((a : v.adicCompletionIntegers F)) * (q : v.adicCompletionIntegers F)
        + (b : v.adicCompletionIntegers F) * (n : v.adicCompletionIntegers F) = 1 := by
      have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hab
      push_cast at this
      exact this
    have hnu : ¬ IsUnit (-((a : v.adicCompletionIntegers F) * (q : v.adicCompletionIntegers F))) := by
      rw [IsUnit.neg_iff]
      exact fun h => hq (isUnit_of_mul_isUnit_right h)
    have hbn := unit_add_nonunit isUnit_one hnu
    rw [← hab', add_neg_cancel_comm] at hbn
    exact isUnit_of_mul_isUnit_right hbn
  have hder : ¬ (q : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hdisc
    have e : tr ^ 2 - 4 * nm = (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) := by ring
    rw [e, hk]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  set f : Polynomial (v.adicCompletionIntegers F) :=
    Polynomial.X ^ 2 - Polynomial.C (tr : v.adicCompletionIntegers F) * Polynomial.X
      + Polynomial.C (nm : v.adicCompletionIntegers F) with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hev : ∀ x, f.eval x = x ^ 2 - (tr : v.adicCompletionIntegers F) * x + nm := by
    intro x
    simp [hf]
  have hdev : ∀ x, (Polynomial.derivative f).eval x = 2 * x - (tr : v.adicCompletionIntegers F) := by
    intro x
    simp only [hf, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    push_cast
    ring
  have h0 : ¬ IsUnit (f.eval (r : v.adicCompletionIntegers F)) := by
    rw [hev]
    have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hk
    push_cast at this
    rw [this]
    exact fun h => hq (isUnit_of_mul_isUnit_left h)
  have h1 : IsUnit ((Polynomial.derivative f).eval (r : v.adicCompletionIntegers F)) := by
    rw [hdev]
    have := hint _ hder
    push_cast at this
    exact this
  obtain ⟨ρ, hρ, hρr⟩ := hH F v f r hmon h0 h1
  refine ⟨ρ, ?_, ?_⟩
  · rw [hev] at hρ
    exact hρ
  · have h2 : ¬ IsUnit (2 * (ρ - (r : v.adicCompletionIntegers F))) :=
      fun h => hρr (isUnit_of_mul_isUnit_right h)
    have h3 := unit_add_nonunit ((hdev _) ▸ h1) h2
    have e : 2 * (r : v.adicCompletionIntegers F) - tr + 2 * (ρ - r) = 2 * ρ - tr := by ring
    rw [e] at h3
    exact h3
end

section

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem congr_core {n : ℕ} {B : Type*} [CommRing B] (σ : B →+* B)
    (Nb N'b Mb X X' : Matrix (Fin n) (Fin n) B) (τ τ' s z : B)
    (hz : IsUnit z) (hX : IsUnit X.det) (hX' : IsUnit X'.det)
    (hτ : τ' = s * τ * (z * σ z))
    (h : X * Nb * (X.map σ)ᵀ = τ • Mb)
    (h' : X' * N'b * (X'.map σ)ᵀ = τ' • Mb) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ N'b = Pᵀ * (s • Nb) * P.map σ := by
  have hW : X'⁻¹ * X' = 1 := Matrix.nonsing_inv_mul _ hX'
  have hW' : (X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hW]
    simp
  have hWd : IsUnit (X'⁻¹).det := by
    have : (X'⁻¹).det * X'.det = 1 := by rw [← Matrix.det_mul, hW, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  have hzX : (z • X).map σ = σ z • X.map σ := by
    ext i j
    simp
  refine ⟨(X'⁻¹ * (z • X))ᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_smul]
    exact hWd.mul ((hz.pow _).mul hX)
  · have hP : ((X'⁻¹ * (z • X))ᵀ).map σ = σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
      have e : (X'⁻¹ * (z • X)).map σ = (X'⁻¹).map σ * (σ z • X.map σ) := by
        rw [Matrix.map_mul, hzX]
      rw [Matrix.transpose_map, e, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul]
    rw [Matrix.transpose_transpose, hP]
    calc N'b = X'⁻¹ * X' * N'b * ((X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
          rw [hW, hW', Matrix.one_mul, Matrix.mul_one]
      _ = X'⁻¹ * (X' * N'b * (X'.map σ)ᵀ) * ((X'⁻¹).map σ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X'⁻¹ * ((s * (z * σ z)) • (X * Nb * (X.map σ)ᵀ)) * ((X'⁻¹).map σ)ᵀ := by
          rw [h', h, hτ, smul_smul]
          congr 3
          ring
      _ = X'⁻¹ * (z • X) * (s • Nb) * (σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
          congr 1
          ring

theorem pCongrScale : CongrScale := by
  intro E _ _ _ n M N N' K _ _ θ D hθ hD t t' a b s ht' ht X X' hX hX' h h'
  let F := maximalRealSubfield E
  let B := K ⊗[F] E
  let σ := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  let cB : K →+* B := algebraMap K B
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hmul : ∀ x y : E, inE K (x * y) = inE K x * inE K y := fun x y => by
    simp [inE, Algebra.TensorProduct.tmul_mul_tmul]
  have hrat : ∀ q : ℚ, inE K (q : E) = cB (q : K) := fun q => by
    have e : ((Algebra.TensorProduct.includeRight : E →ₐ[F] B) : E →+* B).comp (Rat.castHom E) =
        cB.comp (Rat.castHom K) := RingHom.ext_rat _ _
    exact congrArg (fun f : ℚ →+* B => f q) e
  have hint : inE K (D : E) = cB (D : K) := by
    have := hrat (D : ℚ)
    simpa using this
  set z : B := cB a + cB b * inE K θ with hzdef
  have hσθ : σ (inE K θ) = -inE K θ := by
    show (1 : K) ⊗ₜ[F] (IsCMField.complexConj E θ) = _
    rw [hθ, TensorProduct.tmul_neg]
  have hσc : ∀ x : K, σ (cB x) = cB x := fun x => σ.commutes x
  have hσz : σ z = cB a - cB b * inE K θ := by
    rw [hzdef, map_add (f := _), map_mul, hσc, hσc, hσθ]
    ring
  have hθθ : inE K θ * inE K θ = cB (D : K) := by
    rw [← hmul, ← pow_two, hD, hint]
  have hnorm : z * σ z = cB (a ^ 2 - D * b ^ 2) := by
    rw [hσz, hzdef, map_sub, map_mul, map_pow, map_pow]
    linear_combination (-(cB b) ^ 2) * hθθ
  have hu : (a ^ 2 - D * b ^ 2) ≠ 0 := fun h0 => ht' (by rw [ht, h0, mul_zero])
  have hzu : IsUnit z := by
    have : IsUnit (z * σ z) := by
      rw [hnorm]
      exact (IsUnit.mk0 _ hu).map cB
    exact isUnit_of_mul_isUnit_left this
  have hsm : ∀ (c : K) (A : Matrix (Fin n) (Fin n) B), c • A = cB c • A := fun c A => by
    ext i j
    simp [Algebra.smul_def, cB]
  obtain ⟨P, hP, hE⟩ := congr_core (σ : B →+* B) (N.map (inE K)) (N'.map (inE K)) (M.map (inE K)) X X'
    (cB t) (cB t') (inE K (s : E)) z hzu hX hX' (by
      have hn2 : z * (σ : B →+* B) z = cB (a ^ 2 - D * b ^ 2) := hnorm
      rw [hn2, hrat, ht, map_mul, map_mul])
    (by rw [← hsm]; exact h) (by rw [← hsm]; exact h')
  refine ⟨P, hP, ?_⟩
  have hN : ((s : E) • N).map (fun x => (1 : K) ⊗ₜ[F] x) = inE K (s : E) • N.map (inE K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact hmul _ _
  rw [hN]
  exact hE

end UpperTheory.Gal.G1
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pSplitRep :
    SplitRep := by
  intro R _ tr nm ρ hρ hd u
  obtain ⟨w, hw⟩ := hd.exists_right_inv
  refine ⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩
  unfold qf
  linear_combination ((u - 1) * w) ^ 2 * hρ + (u - 1) * hw
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pZUnitNorm :
    PadicUnitNorm → ZUnitNorm := by
  intro hP v D hv u hu
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hint : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v z‖ ≤ 1 := by
    intro z hz
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo
      ((HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v).2 hz)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hn : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
    apply le_antisymm (hint u hu.le)
    have h1 := hint u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hne : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u ≠ 0 := fun h =>
      hu0 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
        (h.trans (map_zero _).symm))
    exact (inv_le_one₀ (norm_pos_iff.2 hne)).1 h1
  have hdiv : ¬ ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ 2 * D := by
    intro hd
    apply hv
    have hm : 2 * D ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
      Ideal.mem_span_singleton.2 hd
    rw [Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_map_of_equiv] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hid : Rat.IsIntegralClosure.intEquiv ℤ x = x := by
      simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) x
    rw [hid] at hxe
    rw [← hxe]
    exact hx
  obtain ⟨x, y, hxy⟩ := hP _ D hdiv _ hn
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm y, ?_⟩
  have h2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hxy
  simpa using h2
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pHenselV :
    HenselV := by
  intro F _ _ v f a₀ hf h0 h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers F)
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
  obtain ⟨a, ha, hm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) f hf a₀
    (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h0)
    (h1.map (Ideal.Quotient.mk _))
  refine ⟨a, ha, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm
end
