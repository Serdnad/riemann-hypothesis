module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
public import GroundTheory.GlobalFields.Adele.Bundle003
public import GroundTheory.GlobalFields.Adele.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.Bundle001
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import GroundTheory.GlobalFields.Adele.Bundle002
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacDbl

theorem boxFun_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inl) (by fun_prop)).mul
    (h₂.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  have hK : IsCompact ((fun p : (κ → R) × (κ' → R) => Sum.elim p.1 p.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) := by
    refine (IsCompact.prod h₁.2 h₂.2).image (continuous_pi ?_)
    rintro (i | i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra hne
  obtain ⟨e₁, e₂⟩ := mul_ne_zero_iff.1 hne
  refine hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ e₁, subset_tsupport _ e₂⟩, ?_⟩
  funext i
  rcases i with i | i <;> rfl

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end

end GlobalTheory.CompanionTheory.VacDbl
end
end

section

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

theorem _root_.GlobalTheory.T.lagrangian_stabilizer_character_trivial : ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] (E : Type) [CommRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsQuad c ξ → IsHerm c J → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelChar.char_trivial | exact GlobalTheory.CompanionTheory.SiegelChar.char_trivial | (intros; apply GlobalTheory.CompanionTheory.SiegelChar.char_trivial <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.SplitRatio

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]


open GroundTheory.Global in
theorem exists_schA_compact : ∃ Φ ∈ schA F κ, Continuous Φ ∧ HasCompactSupport Φ ∧ Φ 0 ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := default
  have hb : HasCompactSupport fun v => (b v : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) := hb.toSchwartzMap hb'
  have hf : ∀ v, f v = (b v : ℂ) := fun _ => rfl
  set O := Set.univ.pi fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO
  set g := O.indicator fun _ => (1 : ℂ) with hgd
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have hc : IsCompact O := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
    have ho : IsOpen O := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
    have hcl : IsClosed O := isClosed_set_pi fun _ _ =>
      AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup GroundTheory.Global.isOpen_integralFiniteAdeles
    refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ O
    · exact ⟨_, ho, hx, fun y hy => by rw [hgd, Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [hgd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, _, hg, rfl⟩, ?_, ?_, ?_⟩
  · refine (f.continuous.comp (continuous_pi fun i => ?_)).mul (hg.1.continuous.comp (continuous_pi fun i => ?_))
    · exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · let m : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
      fun p i => ((GroundTheory.Global.homeomorphMixedSpace F).symm (p.1 i), p.2 i)
    have hm : Continuous m := continuous_pi fun i =>
      ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply i).comp continuous_snd)
    refine HasCompactSupport.intro ((hb.isCompact.prod hg.2.isCompact).image hm) fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
    refine hx ⟨(_, _), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩
    exact Prod.ext ((GroundTheory.Global.homeomorphMixedSpace F).symm_apply_apply (x i).1) rfl
  · have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ O := fun i _ => Subring.zero_mem _
    have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 :=
      funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [pureA, h1, hf, hgd, Set.indicator_of_mem h0,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    simp

end GlobalTheory.CompanionTheory.SplitRatio
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.IdxAd.Unif

theorem resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by
  intro F _ _ v
  have hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) =
      (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr hS
  have hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F] := fun hx =>
    (GroundTheory.Global.mem_valuationInteger_iff v _).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)
  refine ⟨?_, ?_⟩
  · have h := GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
    rw [← h]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  · obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
    have hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      GroundTheory.Global.valued_of_irreducible v hq
    have hq0 : (q : v.adicCompletion F) ≠ 0 := fun h => hq.ne_zero (Subtype.ext h)
    have hp : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff e.symm).2 hq
    refine ⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩
    have ht : Valued.v (t : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.2 t.ne_zero
    set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha
    have hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) :
        v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval,
        ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]
      simp
    refine ⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · simp [mul_assoc]
    · rw [ha, Int.natAbs_neg]

end GlobalTheory.CompanionTheory.IdxAd.Unif
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WittOrbit

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem int_mul {l m n : Type} [Fintype m] {X : Matrix l m E} {Y : Matrix m n E} (hX : ∀ i j, X i j ∈ A)
    (hY : ∀ i j, Y i j ∈ A) : ∀ i j, (X * Y) i j ∈ A := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by
  intro i j
  rw [Matrix.map_apply]
  exact hs _ (hX i j)

theorem map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]

theorem map_mul' {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul

end

end GlobalTheory.CompanionTheory.WittOrbit
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.MatSat

theorem exists_basis_cols {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)
  obtain ⟨φ⟩ : Nonempty (Fin n ≃ β) :=
    ⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b) :=
    ⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩
  have hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ)) := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]
    omega
  obtain ⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans
      (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O,
      P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm) := ⟨_, rfl⟩
  have hPdet : IsUnit P.det := by
    letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)
    rw [hPdef]
    exact Matrix.isUnit_det_of_invertible _
  have hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i := by
    intro i b
    show P i (Sum.inl b) = _
    rw [hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply,
      Equiv.symm_symm, he]
  have hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O) := by
    intro b
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (S.bN (φ.symm b)).2
    exact ⟨v, hv⟩
  choose pre hpre using hpre
  obtain ⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i :=
    ⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩
  have ha : ∀ b, S.a (φ.symm b) ≠ 0 := by
    intro b h
    have h1 := S.snf (φ.symm b)
    rw [h, zero_smul] at h1
    exact S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)
  obtain ⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b =
      S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') *
        S.a (φ.symm b') :=
    ⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
      (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩
  refine ⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩
  · ext i b
    rw [Matrix.mul_diagonal, hP1, Matrix.mul_apply]
    have h1 := congrFun (hpre b) i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [hs]
    rw [h1, S.snf, hf']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext i b
    have hw := S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
    have hw' := congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S.snf] at hw'
    have hcol : (A.mulVecLin (Pi.single b 1)) i = A i b := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Matrix.mul_apply]
    refine hcol.symm.trans (hw'.symm.trans ?_)
    simp only [hP1, hu, hf']
    refine Fintype.sum_equiv φ _ _ fun k => ?_
    simp only [Equiv.symm_apply_apply]
    ring

theorem exists_saturation {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by
  classical
  obtain ⟨L, hL⟩ := hC
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : (β ⊕ γ) × β => C p.1 p.2)
  have hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O,
      algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2 := by
    intro p
    obtain ⟨x, hx⟩ := RingHom.mem_rangeS.1 (hb p)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hbne : algebraMap O K (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O,
      C₁.map (algebraMap O K) = algebraMap O K (b : O) • C :=
    ⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩
  have hinj : Function.Injective C₁.mulVecLin := by
    intro v w hvw
    have h1 : C₁ *ᵥ v = C₁ *ᵥ w := hvw
    have h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) =
        algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x)) := by
      intro x
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hC₁]
      first
      | rw [Matrix.smul_mulVec]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e1 := h2 v
    have e2 := h2 w
    rw [h1] at e1
    have h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w) :=
      smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)
    have h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w := by
      have := congrArg (fun z => L *ᵥ z) h3
      simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
    funext i
    exact IsFractionRing.injective O K (congrFun h4 i)
  obtain ⟨P, a, s, u, hP, -, -, hu⟩ := exists_basis_cols C₁ hinj
  have hCw : C = (P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) := by
    have e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K)) := by
      rw [← hC₁, hu, Matrix.map_mul]
    rw [Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hLw : (L * P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1 := by
    rw [Matrix.mul_assoc, ← hCw, hL]
  have hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) *
      (L * P.toCols₁.map (algebraMap O K)) = 1 := by
    first
    | exact mul_eq_one_comm.1 hLw
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw
  refine ⟨⟨L * P.toCols₁.map (algebraMap O K),
    (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩
  · show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)
    rw [hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]
  · rw [Matrix.fromCols_toCols]
    exact hP

end GlobalTheory.CompanionTheory.MatSat
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CommonTransversal

theorem exists_skew_isUnit_det {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by
  classical
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a
  obtain ⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hD
  have hP1 : P.det = 1 := by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ1 : Q.det = 1 := by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1 := by
    intro M hM
    rw [Matrix.det_transpose]
    have e : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    rw [e, hM, map_one]
  have cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0 := by
    intro M x hM hx
    have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
    calc x = x ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv (A := M) hu, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hx, Matrix.zero_vecMul]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = z - σ z := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)
  have hσc : σ c = -c := by rw [hcdef, map_sub, hσ]; ring
  obtain ⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0) :=
    ⟨_, rfl⟩
  have hss : (s0.map σ)ᵀ = -s0 := by
    rw [hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]
    congr 1
    funext i
    split_ifs <;> simp [hσc]
  have hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q := by
    ext i j
    simp [hσ]
  have hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ := by
    rw [hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]
  refine ⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    have e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q := by
      rw [hD]
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    have h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0 :=
      cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)
    have h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0 := by
      simpa only [Matrix.vecMul_vecMul, Matrix.vecMul_add] using h0
    have hE : ∀ j, (v ᵥ* P) j * D j +
        ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0 := by
      intro j
      have e := congr_fun h0' j
      rw [Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal] at e
      exact e
    have hwD : (v ᵥ* P) ᵥ* diagonal D = 0 := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.zero_apply]
      by_cases hDj : D j = 0
      · rw [hDj, mul_zero]
      · have e := hE j
        rw [if_neg hDj, mul_zero, add_zero] at e
        rw [(mul_eq_zero.1 e).resolve_right hDj, zero_mul]
    have hva : v ᵥ* a = 0 := by
      rw [hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]
    have hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0 := by rw [h, Matrix.vecMul_zero]
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul,
      zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hc1
    have hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0 :=
      cancel _ _ (hst1 P hP1) hc1
    have hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0 := by
      funext j
      rw [Pi.zero_apply]
      by_cases hDj : D j = 0
      · have e := hE j
        rw [if_pos hDj, hDj, mul_zero, zero_add] at e
        exact (mul_eq_zero.1 e).resolve_right hc
      · have e := congr_fun hud j
        rw [Matrix.vecMul_diagonal, Pi.zero_apply] at e
        exact (mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)
    exact hv v hva (cancel _ _ (hst1 Q hQ1) hu)

end GlobalTheory.CompanionTheory.CommonTransversal
end
