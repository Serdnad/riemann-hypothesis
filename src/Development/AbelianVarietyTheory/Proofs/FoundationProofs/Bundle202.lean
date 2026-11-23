module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Formalism.LocalRingCardinality.Bundle005
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle176
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle195
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def ClassTermBound : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * (T / Ω))

def ClassTermBoundBeta : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∀ Λ : PeriodPair, Λ.ω₁ = 1 → Λ.ω₂ = (1 + Complex.I * (Real.sqrt H.d : ℝ)) / 2 →
      ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * beta H.E H.d s κ Λ T)

theorem intAt_of_pow {l m : ℕ} (hm : 0 < m) {a : ℂ} (h : IntAt l (a ^ m)) : IntAt l a := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, IsIntegral.of_pow hm ?_⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : IsIntegral ℤ ((n : ℂ) ^ m) := (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))).pow m |> fun h => by simpa using h
  have e : ((n : ℂ) * a) ^ (m + 1) = (n : ℂ) ^ m * ((n : ℂ) * a ^ (m + 1)) := by ring
  rw [e]
  exact h1.mul h

theorem intAt_natMul {l : ℕ} (k : ℕ) {a : ℂ} (h : IntAt l a) : IntAt l ((k : ℂ) * a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  have h1 : IsIntegral ℤ (k : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))
  rw [mul_left_comm]
  exact h1.mul h

def ringPair (d : ℕ) (hd : 0 < d) : PeriodPair where
  ω₁ := 1
  ω₂ := (1 + Complex.I * (Real.sqrt d : ℝ)) / 2
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp at hi hr
    have hb : b = 0 := by
      rcases hi with hi | hi
      · exact hi
      · omega
    subst hb
    simpa using hr

theorem classTermBound_of_beta (h : ClassTermBoundBeta) : ClassTermBound := by
  intro R H I _ φ s κ 𝔣 χ hD
  have hd : 0 < H.d := H.hypOdd.2.1.pos
  set Λ := ringPair H.d hd
  have hC : ((C0 H.E H.d (2 * s) κ : ℝ) : ℂ) ≠ 0 := by
    have := hD.2.2.1
    exact_mod_cast (cmValueConst_pos H.E hd (by omega) κ).ne'
  have hΔ : latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (latDisc_ne_zero Λ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) (n := 12) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hz]; simp)
  refine ⟨z / C0 H.E H.d (2 * s) κ, div_ne_zero hz0 hC, fun l hl => ?_⟩
  obtain ⟨N, hN⟩ := h R H I φ s κ 𝔣 χ hD Λ rfl rfl l hl
  refine ⟨N, fun Q hQ hQl y T hT => intAt_of_pow (m := 12) (by norm_num) ?_⟩
  have := intAt_natMul (l ^ (11 * N)) (hN Q hQ hQl y T hT)
  convert this using 1
  unfold beta
  rw [← hz]
  push_cast
  field_simp
  ring

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ}

theorem isIntegral_of_intAt (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (ι : ℂ →+* AlgebraicClosure (FractionRing O)) {a : ℂ}
    (h : IntAt l a) : IsIntegral O (ι a) := by
  obtain ⟨n, hn, h⟩ := h
  have hu : IsUnit (n : O) := by
    by_contra hu
    have hn' : (n : O) ∈ IsLocalRing.maximalIdeal O := hu
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hn
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : (x : O) * n + (y : O) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hxy
      rw [← this]
      exact add_mem (Ideal.mul_mem_left _ _ hn') (Ideal.mul_mem_left _ _ hl)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have h2 : IsIntegral O (ι ((n : ℂ) * a)) := h.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := v)).mul h2
  have h4 := congrArg (algebraMap O (AlgebraicClosure (FractionRing O))) hv
  rw [map_mul, map_natCast, map_one] at h4
  rwa [map_mul, map_natCast, ← mul_assoc, h4, one_mul] at h3

theorem exists_pow_mul_isIntegral (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (u : AlgebraicClosure (FractionRing O)) :
    ∃ M : ℕ, IsIntegral O ((l : AlgebraicClosure (FractionRing O)) ^ M * u) := by
  have ha : IsAlgebraic O u :=
    (IsFractionRing.isAlgebraic_iff O (FractionRing O) _).2 (Algebra.IsAlgebraic.isAlgebraic u)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hl
  refine ⟨n, ?_⟩
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := c ^ n * (↑v⁻¹ : O))).mul hint
  refine (congrArg (IsIntegral O) ?_).mpr h3
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← map_natCast (algebraMap O (AlgebraicClosure (FractionRing O))), ← map_pow, hc]
  congr 2
  rw [mul_assoc, ← mul_assoc (↑v⁻¹ : O), Units.inv_mul, one_mul, mul_pow, mul_comm]

theorem exists_eq_of_isIntegral {x : FractionRing O}
    (h : IsIntegral O (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O)) x)) :
    ∃ y : O, algebraMap O (FractionRing O) y = x :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff ).1 h)

end Integral

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_bound_at (h : ClassTermBound) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) :
    ∃ n : ℕ, ∀ Q, BlochKatoReduction.Gen.QOk X i Q → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, -, hth⟩ := ht
  obtain ⟨Ω, hΩ, hb⟩ := h D.R D.host I φ s κ 𝔣 χ hD
  obtain ⟨n, hn⟩ := hb (X.l i) (X.lPrime i).out
  obtain ⟨M, hM⟩ := exists_pow_mul_isIntegral (X.O_l i) (u * ι Ω)
  refine ⟨M + n, fun Q hQ δ => exists_eq_of_isIntegral ?_⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth Q hQ
  obtain ⟨h1, h2⟩ := placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣
  have hf : ({q | π q⁻¹ = δ} : Set (PicO (condQ 𝔣 (belowSet Q)))).Finite := Set.toFinite _
  have hs : IsIntegral (X.O i) (∑ q ∈ hf.toFinset, ι (((X.l i : ℕ) : ℂ) ^ n * (T q / Ω))) :=
    IsIntegral.sum _ fun q _ => isIntegral_of_intAt (X.O_l i) ι (hn _ h1 h2 _ _ (hT q))
  refine (congrArg (IsIntegral (X.O i)) ?_).mpr (hM.mul hs)

  rw [map_mul, map_pow, map_natCast, hδ, finsum_mem_eq_finite_toFinset_sum _ hf, ← map_sum, ← Finset.mul_sum, ← Finset.sum_div,
  map_mul, map_pow, map_natCast, map_div₀]
  have : ι Ω ≠ 0 := (map_ne_zero ι).2 hΩ
  field_simp
  ring

variable (X)

theorem exists_gen_bound (h : ClassTermBound) (ht : IsToricElt X) : ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 := by
  classical
  have key : ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ n : ℕ, X.NonzeroIndexPlace i → ∀ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s → ∀ Q, BlochKatoReduction.Gen.QOk X i Q →
      ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
        ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
    intro i lam
    by_cases hx : X.NonzeroIndexPlace i ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s
    · obtain ⟨hi, s, hs⟩ := hx
      obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
      obtain ⟨ι, -, hι⟩ := ht i hi
      obtain ⟨n, hn⟩ := exists_bound_at h (hι lam s hs)
      exact ⟨n, fun _ _ _ => hn⟩
    · exact ⟨0, fun hi s hs => (hx ⟨hi, s, hs⟩).elim⟩
  choose n hn using key
  refine ⟨fun i => Finset.univ.sup (n i), fun i hi Q hQ lam s hs δ => ?_⟩
  obtain ⟨y, hy⟩ := hn i lam hi s hs Q hQ δ
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n i) (Finset.mem_univ lam))
  refine ⟨((X.l i : ℕ) : X.O i) ^ k * y, ?_⟩
  rw [map_mul, map_pow, map_natCast, hy]
  show _ = _ ^ (Finset.univ.sup (n i)) * _
  rw [hk]
  ring

end Record

end GlobalTheory.ToricDenom
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.LevelOneLocal

theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem tendsto_E₄ : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨2, rfl⟩

theorem tendsto_E₆ : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨3, rfl⟩

theorem cube_sub_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero τ
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

theorem isMF_E₄ : IsMF ⊤ 4 (E₄ : ℍ → ℂ) := isMF_coe_top E₄

theorem isMF_E₆ : IsMF ⊤ 6 (E₆ : ℍ → ℂ) := isMF_coe_top E₆

theorem differentiableAt_comp {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    DifferentiableAt ℂ (f ∘ ofComplex) τ :=
  mdifferentiableAt_iff.mp (hf τ)

theorem deriv_comb (α β : ℂ) (τ : ℍ) :
    deriv ((α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex) τ =
      α * (3 * E₄ τ ^ 2 * deriv (⇑E₄ ∘ ofComplex) τ) - β * (2 * E₆ τ * deriv (⇑E₆ ∘ ofComplex) τ) := by
  have h4 := (differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt
  have h6 := (differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt
  have h := ((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)
  have e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex =
      fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2 := by
    ext x; simp
  rw [e, h.deriv]
  simp

theorem exists_local_data : ∀ τ₀ : ℍ, ∃ (n : ℕ) (a b : ℤ) (E : ℍ → ℂ) (u : SL(2, ℤ)), u • τ₀ = τ₀ ∧ 0 < n ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) n ∧ a < b ∧ Even (b - a) ∧ IsMF ⊤ b E ∧ (∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀) ∧ (∃ c : ℂ, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) ∧ ∀ d : ℤ, 0 ≤ d → (n : ℤ) ∣ d → ∃ e : ℍ → ℂ, IsMF ⊤ (d + a) e ∧ e τ₀ ≠ 0 := by
  intro τ₀
  have hD := cube_sub_sq_ne_zero τ₀
  by_cases h6 : E₆ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).1 h6
    have h4 : E₄ τ₀ ≠ 0 := fun h => hD (by simp [h, h6])
    refine ⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h6, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩
      have := isMF_E₄.pow m
      convert this using 1
      push_cast; ring
  by_cases h4 : E₄ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).2 h4
    refine ⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h4, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩
      have := isMF_E₆.pow m
      convert this using 1
      push_cast; ring
  refine ⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_,
    by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩,
    ?_⟩
  · rw [ModularGroup.SL_neg_smul, one_smul]
  · have : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1 := by simp [denom]
    rw [this]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · exact ((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)
  · have hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0 := by simpa using hτ
    refine ⟨?_, GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by linear_combination hz)⟩
    have hDτ := cube_sub_sq_ne_zero τ
    have k4 : E₄ τ ≠ 0 := by
      intro h
      have : E₆ τ = 0 := by simpa [h, h4] using hz
      exact hDτ (by simp [h, this])
    rw [deriv_comb]
    intro h
    have hW := GlobalTheory.T.eisenstein_wronskian_ne_zero τ
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW
    linear_combination (2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h
  · have := ((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))
    simp only [one_pow, mul_one] at this
    exact this
  · rintro d hd ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
    rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
    · refine ⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩
      have := isMF_E₄.pow (p + 1)
      convert this using 1
      push_cast; ring
    · refine ⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩
      exact mul_ne_zero (pow_ne_zero p h4) h6

end GlobalTheory.LevelOneLocal
end

section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def eigIdxFiniteTypes (D : D7) (X : DivX D) : EigIdx D X where
  Pi := D.what₂.FT
  fin := D.what₂.instFT
  dec := D.what₂.instFTd
  cOf := id
  lam_const := by
    intro j _ π π' e _ _ h
    have h' : π = π' := h
    rw [h']

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

theorem _root_.GlobalTheory.T.nonempty_compactDualHaar : Nonempty CDHaar := by
  first | exact @GlobalTheory.CompactDualExists.nonempty_cdHaar | exact GlobalTheory.CompactDualExists.nonempty_cdHaar | (intros; apply GlobalTheory.CompactDualExists.nonempty_cdHaar <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact : ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V), IrrGK M → IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' → ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  first | exact @GlobalTheory.exists_intertwiner_map_highestVector | exact GlobalTheory.exists_intertwiner_map_highestVector | (intros; apply GlobalTheory.exists_intertwiner_map_highestVector <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible : ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ} (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)), (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) → (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) → (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) → ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  first | exact @GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | exact GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | (intros; apply GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | exact GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | (intros; apply GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankin_dirichlet_series_identity_hecke : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EisM.rankin_dirichlet_identity | exact GlobalTheory.EisM.rankin_dirichlet_identity | (intros; apply GlobalTheory.EisM.rankin_dirichlet_identity <;> assumption)
end
