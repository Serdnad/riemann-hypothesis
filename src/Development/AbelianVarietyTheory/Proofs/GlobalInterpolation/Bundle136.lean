module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.IdxDet

open GlobalTheory.LatBasisAt

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (w : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt w a ↔ a ∈ locRing w := by
  rw [mem_locRing]
  constructor
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [← h]; field_simp⟩
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [h]; field_simp⟩

theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (a : locRing P) : P.valuation E (a : E) ≤ 1 :=
  GlobalTheory.CharValCompare.intAt_iff.1 ((intAt_iff_mem P _).2 a.2)

theorem val_unit (P : HeightOneSpectrum (𝓞 E)) (u : (locRing P)ˣ) :
    P.valuation E ((u : locRing P) : E) = 1 := by
  have h : P.valuation E ((u : locRing P) : E) * P.valuation E (((u⁻¹ : (locRing P)ˣ) : locRing P) : E) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  refine le_antisymm (val_le_one P _) ?_
  rw [← h]
  exact mul_le_of_le_one_right' (val_le_one P _)

theorem val_irreducible (P : HeightOneSpectrum (𝓞 E)) [IsDiscreteValuationRing (locRing P)]
    {p : locRing P} (hp : Irreducible p) : P.valuation E (p : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ1 : π ∈ locRing P := by
    rw [← intAt_iff_mem, GlobalTheory.CharValCompare.intAt_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hπ0 : (⟨π, hπ1⟩ : locRing P) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hp
  have h1 : π * ((u : locRing P) : E) = (p : E) ^ k := by
    simpa using congrArg Subtype.val hu
  have h2 := congrArg (P.valuation E) h1
  rw [map_mul, val_unit, mul_one, hπ, map_pow] at h2
  have hp0 : P.valuation E (p : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hp.ne_zero (Subtype.ext h)
  have hle := val_le_one P p
  rw [← WithZero.exp_log hp0] at h2 hle ⊢
  generalize WithZero.log (P.valuation E (p : E)) = a at h2 hle ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  congr 1
  have : a ∣ 1 := ⟨-k, by linarith⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h
  · omega
  · exact h

theorem relIndex_mulVec : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (M : Matrix ι ι E) (L₀ L₁ : AddSubgroup (ι → E)), M.det ≠ 0 → (∀ x, x ∈ L₀ ↔ ∀ i, IntAt P (x i)) → (∀ x, x ∈ L₁ ↔ ∃ y ∈ L₀, x = M.mulVec y) → L₁ ≤ L₀ → ((L₁.relIndex L₀ : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ ordE P M.det := by
  intro E _ _ ι _ _ P M L₀ L₁ hdet h0 h1 hle
  haveI := P.isPrime
  haveI := P.isMaximal
  haveI : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot (locRing P)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (locRing P)
  have hent : ∀ i j, M i j ∈ locRing P := by
    intro i j
    have hs : (Pi.single j 1 : ι → E) ∈ L₀ := by
      rw [h0]
      intro k
      rw [intAt_iff_mem, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have := (h0 _).1 (hle ((h1 _).2 ⟨_, hs, rfl⟩)) i
    rw [intAt_iff_mem] at this
    simpa using this
  let N : Matrix ι ι (locRing P) := Matrix.of fun i j => ⟨_, hent i j⟩
  have hN : N.map (algebraMap (locRing P) E) = M := by
    ext i j; rfl
  have hNd : ((N.det : locRing P) : E) = M.det := by
    rw [← hN]
    exact RingHom.map_det (algebraMap (locRing P) E) N
  have hne : N.det ≠ 0 := by
    intro h
    rw [h] at hNd
    exact hdet hNd.symm
  have hinj : Function.Injective (Matrix.toLin' N) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hv
  obtain ⟨m, ⟨v, hv⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (locRing P) ι) hp _ hinj
  rw [LinearMap.det_toLin'] at hv
  have hord : ordE P M.det = m := by
    have e1 : M.det * ((v : locRing P) : E) = (p : E) ^ m := by
      rw [← hNd]; exact_mod_cast congrArg Subtype.val hv
    have e2 := congrArg (P.valuation E) e1
    rw [map_mul, val_unit, mul_one, map_pow, val_irreducible P hp, ← WithZero.exp_nsmul] at e2
    unfold ordE
    rw [e2, WithZero.log_exp]
    simp
  have hq : Nat.card (locRing P ⧸ Ideal.span {p}) = Ideal.absNorm P.asIdeal := by
    rw [← hp.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (locRing P)).toEquiv).symm
  let e : (ι → locRing P) →+ (ι → E) :=
    { toFun := fun x i => (x i : E)
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hei : Function.Injective e := by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  have hW0 : L₀ = AddSubgroup.map e ⊤ := by
    ext x
    rw [h0]
    constructor
    · intro hx
      exact ⟨fun i => ⟨_, (intAt_iff_mem P _).1 (hx i)⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩ i
      exact (intAt_iff_mem P _).2 (y i).2
  have hcomm : ∀ y, M.mulVec (e y) = e (Matrix.toLin' N y) := by
    intro y
    funext i
    rw [← hN]
    exact (RingHom.map_mulVec (algebraMap (locRing P) E) N y i).symm
  have hW1 : L₁ = AddSubgroup.map e (LinearMap.range (Matrix.toLin' N)).toAddSubgroup := by
    ext x
    rw [h1, hW0]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (hcomm y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, trivial, rfl⟩, (hcomm y).symm⟩
  have : L₁.relIndex L₀ = Ideal.absNorm P.asIdeal ^ m := by
    rw [hW1, hW0, AddSubgroup.relIndex_map_map_of_injective _ _ hei, AddSubgroup.relIndex_top_right, ← hq]
    exact hc
  rw [this, hord, zpow_natCast, Nat.cast_pow]

end GlobalTheory.IdxDet
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.OrdDetConj

open GlobalTheory.CharValCompare

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem ordE_mul (P : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordE P (a * b) = ordE P a + ordE P b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem exists_ordE_star (P : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℤ, 0 ≤ m ∧ ∀ a : E, a ≠ 0 → ordE (conjPrime₂ P) (star a) = m * ordE P a := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hs0 : (conjPrime₂ P).valuation E (star π) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 hπ0)
  refine ⟨ordE (conjPrime₂ P) (star π), ?_, fun a ha => ?_⟩
  · have h1 : (conjPrime₂ P).valuation E (star π) ≤ 1 := intAt_iff.1 (intAt_star (intAt_iff.2 (by
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)))
    unfold ordE
    rw [neg_nonneg, WithZero.log_le_iff_le_exp hs0]
    exact h1
  · have ha' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have hsa : (conjPrime₂ P).valuation E (star a) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 ha)
    have h1 : P.valuation E (a * π ^ (WithZero.log (P.valuation E a))) = 1 := by
      rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      conv_lhs => arg 1; rw [← WithZero.exp_log ha']
      rw [← WithZero.exp_add]
      simp
    have h2 := congrArg WithZero.log (val_star_eq_one h1)
    rw [star_mul', star_zpow₀, map_mul, map_zpow₀, WithZero.log_mul hsa (zpow_ne_zero _ hs0), WithZero.log_zpow,
      WithZero.log_one, smul_eq_mul] at h2
    unfold ordE
    linear_combination -h2

theorem ordE_star (P : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) : ordE (conjPrime₂ P) (star a) = ordE P a := by
  obtain ⟨m, hm, h⟩ := exists_ordE_star P
  obtain ⟨m', hm', h'⟩ := exists_ordE_star (conjPrime₂ P)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : ordE P π = 1 := by
    unfold ordE
    rw [hπ, WithZero.log_exp, neg_neg]
  have h2 := h' (star π) (star_ne_zero.2 hπ0)
  rw [conjP_conjP, star_star, h π hπ0, h1, mul_one] at h2
  have h3 : m = 1 := Int.eq_one_of_mul_eq_one_left hm h2.symm
  rw [h a ha, h3, one_mul]

theorem ordDet_conjP {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ordDet (conjPrime₂ P) N = -ordDet P N := by
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨f', hf'⟩ := exists_isFr (conjPrime₂ P) hN
  have h := val_dual hN hf hf'
  have h0 : star (dt f) ≠ 0 := star_ne_zero.2 (dt_ne _)
  rw [← ordE_eq_zero_iff (mul_ne_zero h0 (dt_ne _)), ordE_mul _ h0 (dt_ne _), ordE_star P (dt_ne _)] at h
  rw [ordDet_eq hf, ordDet_eq hf']
  linear_combination h

theorem finite_pos {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N}.Finite := by
  rcases Set.eq_empty_or_nonempty {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N} with h | ⟨P, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((gen_detI hf).2 _).2 le_rfl)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (zero_mem _)
  have hx0 : s • dt f ≠ 0 := smul_ne_zero hs0 (dt_ne _)
  refine (HeightOneSpectrum.Support.finite (𝓞 E) (s • dt f)⁻¹).subset fun Q hQ => ?_
  obtain ⟨g, hg⟩ := exists_isFr Q hN
  have h1 := ((gen_detI hg).2 _).1 (le_locP Q _ hx)
  have h2 : Q.valuation E (dt g) < 1 := by
    rw [Set.mem_ofPred_eq, ordDet_eq hg, ordE, neg_pos,
      WithZero.log_lt_iff_lt_exp ((Valuation.ne_zero_iff _).2 (dt_ne _))] at hQ
    exact hQ
  show 1 < Q.valuation E (s • dt f)⁻¹
  rw [map_inv₀, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]
  exact h1.trans_lt h2

theorem ordDet_conj_finite : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 E), ordDet (conjPrime₂ P) N = -ordDet P N) ∧ {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite := by
  intro E _ _ _ n N hN
  refine ⟨ordDet_conjP hN, ((finite_pos hN).union ((finite_pos hN).image conjPrime₂)).subset fun Q hQ => ?_⟩
  rcases lt_or_gt_of_ne hQ with h | h
  · refine Or.inr ⟨conjPrime₂ Q, ?_, conjP_conjP Q⟩
    rw [Set.mem_ofPred_eq, ordDet_conjP hN]
    exact neg_pos.2 h
  · exact Or.inl h

end GlobalTheory.OrdDetConj
end
end
