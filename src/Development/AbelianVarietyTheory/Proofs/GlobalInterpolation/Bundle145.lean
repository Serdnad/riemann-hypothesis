module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalIdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle141
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle003
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.Host (HChar atFin IsUnitAt IsUnifAt)
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Neutral.B1

namespace GlobalTheory.TwistVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem evP_toRInt (P : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E) :
    evP F P (toRInt F E b : AfE F E) = algebraMap E (P.adicCompletion E) (b : E) := by
  change afIso F E ((b : E) ⊗ₜ[F] 1) P = _
  rw [afIso_tmul_one]
  rfl

theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : RInt F E} (h : w ∈ P.asIdeal.map (toRInt F E)) :
    Valued.v (evP F P (w : AfE F E)) < 1 := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [evP_toRInt, Formalism.UG.P.levelaf_valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)) hx

theorem val_le_two {P : HeightOneSpectrum (𝓞 E)} {z : RInt F E} (hz : z ∈ (P.asIdeal ^ 2).map (toRInt F E)) :
    Valued.v (evP F P (z : AfE F E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
  GlobalTheory.UnifConj.val_le_of_mem (afIso F E) (afIso_tmul_one F E) (mem_rInt_iff F E) P 2 z hz

theorem exp_neg_two_lt {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) :
    WithZero.exp (-((2 : ℕ) : ℤ)) < Valued.v (algebraMap E (P.adicCompletion E) (b : E)) := by
  rw [GlobalTheory.SuppIdele.val_algebraMap, ← not_le, P.intValuation_le_pow_iff_mem]
  exact hb2

theorem value_of_congr2 (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) {P : HeightOneSpectrum (𝓞 E)} {u : (AfE F E)ˣ}
    {y : RInt F E} (hy : (y : AfE F E) = u) {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) {x : Eˣ} (hx : (x : E) = b)
    (h1 : y - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → y - 1 ∈ Q.asIdeal.map (toRInt F E)) :
    σ ((μ u : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
  have hb := exp_neg_two_lt hb2
  have a1 : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    have := val_le_two h1
    rwa [AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy] at this
  have a2 : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1 := fun Q hQ => by
    have := valued_lt_of_mem (h2 Q hQ)
    rwa [AddSubgroupClass.coe_sub, map_sub, Subring.coe_one, map_one, hy] at this
  set l := finAf F E (localIdele E P (atFin P x)) with hl
  have key : ∀ Q, Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) - 1) < 1 := fun Q => by
    have e1 : evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) * evP F Q (l : AfE F E) = evP F Q (u : AfE F E) := by
      rw [← map_mul, ← Units.val_mul, div_mul_cancel]
    have e2 : evP F Q (l : AfE F E) = ev Q (localIdele E P (atFin P x) : AdeleRing (𝓞 E) E) :=
      GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ Q
    by_cases hQ : Q = P
    · subst hQ
      rw [ev_local_self] at e2
      have e3 : ((atFin Q x : (Q.adicCompletion E)ˣ) : Q.adicCompletion E) = algebraMap E _ (b : E) := by
        rw [← hx]; rfl
      rw [e2, e3] at e1
      rw [← e1, ← sub_one_mul, map_mul] at a1
      by_contra hn
      push_neg at hn
      exact absurd (lt_of_lt_of_le hb (le_mul_of_one_le_left' hn)) (not_lt.2 a1)
    · rw [ev_local_ne hQ] at e2
      rw [e2, mul_one] at e1
      rw [e1]
      exact a2 Q hQ
  have hu : u / l ∈ intU F E := by
    refine (mem_intU_iff (u / l)).2 fun Q => ?_
    change Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E)) = 1
    have := key Q
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)] at this ⊢
    exact Valuation.map_eq_of_sub_lt _ (by simpa using this)
  have hk : u / l ∈ μ.ker := by
    refine ker_of_reads h (map_toIdl_eq_one ht hu fun Q _ => le_exp_neg_one ?_)
    rw [map_sub, map_one]
    exact key Q
  rw [MonoidHom.mem_ker, map_div, div_eq_one] at hk
  rw [hk]
  exact (h _).symm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  intro F E _ _ _ _ _ K _ σ μ ξ h ht P
  have hne : ∀ {b : 𝓞 E}, b ∉ P.asIdeal ^ 2 → (b : E) ≠ 0 := fun {b} hb e =>
    hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  constructor
  · intro hunr
    have hv : ∀ {c : 𝓞 E}, c ∈ P.asIdeal → (hc2 : c ∉ P.asIdeal ^ 2) →
        ((ξ.locK P (Units.mk0 _ (hne hc2)) : ℂˣ) : ℂ) = ((ξ.val P : ℂˣ) : ℂ) := fun {c} hc hc2 => by
      refine congrArg _ (ξ.val_eq hunr _ ?_)
      show Valued.v (algebraMap E (P.adicCompletion E) (c : E)) = _
      exact GlobalTheory.UnifConj.val_of_cong P _ c hc hc2 (by rw [sub_self, map_zero]; exact zero_le')
    obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
      have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
      simpa using this
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ) :=
      (value_of_congr2 h ht a1 hb2 (x := Units.mk0 _ (hne hb2)) rfl a3 a4).trans (hv hb hb2)
    have hex : ∃ k, IsUnifVal μ P k := by
      refine ⟨μ y, fun w _ z z₀ c f1 hc hc2 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy, ← hv hc hc2]
      exact value_of_congr2 h ht f1 hc2 rfl f3 f4
    unfold unifVal
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ b a1 hb hb2 a2 a3 a4)]
    exact hy
  · intro hq q hqe
    set b : 𝓞 E := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) with hbdef
    have hqb : (q : E) = (b : E) := by rw [hqe, hbdef]; simp
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ) := value_of_congr2 h ht a1 hq hqb a3 a4
    have hex : ∃ k, IsQValC μ P k := by
      refine ⟨μ y, fun w _ z z₀ f1 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy]
      exact value_of_congr2 h ht f1 hq hqb f3 f4
    unfold qVal qValC
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ a1 a2 a3 a4)]
    exact hy

end GlobalTheory.TwistVal
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory.RealGal.AttConj

section Gen

variable {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem inv_apply_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g y) = y := by
  show (g⁻¹ * g) y = y
  rw [inv_mul_cancel]
  rfl

theorem apply_inv_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : g ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) = y := by
  show (g * g⁻¹) y = y
  rw [mul_inv_cancel]
  rfl

theorem val_le_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y ≤ 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem val_lt_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff',
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω).injective]

theorem exists_of_fixed [CharZero K] [IsAlgClosure K Ω] (z : Ω) (hz : ∀ t : Formalism.ConjugateSelfDual.G K Ω, t z = z) :
    ∃ y : K, algebraMap K Ω y = z := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω)
  have hz' : z ∈ IntermediateField.fixedField (⊥ : IntermediateField K Ω).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro t _
    exact hz t
  rw [h] at hz'
  exact IntermediateField.mem_bot.1 hz'

theorem exists_ringEquiv (g : Formalism.ConjugateSelfDual.G F Ω)
    (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)) :
    ∃ γ : K ≃+* K, ∀ x, algebraMap K Ω (γ x) = g (algebraMap K Ω x) := by
  choose f hf using h1
  choose f' hf' using h2
  have hinj := (algebraMap K Ω).injective
  let φ : K →+* K :=
    { toFun := f
      map_one' := hinj (by simp [hf])
      map_mul' := fun x y => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun x y => hinj (by simp [hf]) }
  let ψ : K →+* K :=
    { toFun := f'
      map_one' := hinj (by simp [hf'])
      map_mul' := fun x y => hinj (by simp [hf'])
      map_zero' := hinj (by simp [hf'])
      map_add' := fun x y => hinj (by simp [hf']) }
  refine ⟨RingEquiv.ofRingHom φ ψ ?_ ?_, fun x => hf x⟩
  · ext x
    exact hinj (by
      show algebraMap K Ω (f (f' x)) = algebraMap K Ω x
      rw [hf, hf', apply_inv_apply])
  · ext x
    exact hinj (by
      show algebraMap K Ω (f' (f x)) = algebraMap K Ω x
      rw [hf', hf, inv_apply_apply])

variable [NumberField K]

theorem ine_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := K) A) :
    c s ∈ ReciprocityTheory.Gal.Ine (F := K) (g • A) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply]
    exact hs.2 _ hx

theorem frob_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (q : ℕ) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : Formalism.ConjugateSelfDual.IsFrob A q s) :
    Formalism.ConjugateSelfDual.IsFrob (g • A) q (c s) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply, map_pow]
    exact hs.2 _ hx

end Gen

end GlobalTheory.RealGal.AttConj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove
  GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.ThetaMove.LatticeFacts

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) := by
  have h : (Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)
      = -((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)) + (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast; ring

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 := by
  unfold TaylorLogMetric.al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem latAll {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.LatAll := by
  have h0 : δ ≠ 0 := delta_ne_zero B
  refine ⟨fun N N' L L' hA => ⟨?_, fun x _ => al_sign D _ x, ?_⟩, fun N N' L₁ L₁' L₂ L₂' h₁ h₂ =>
    ⟨IO.La_index_ne_zero cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂, IO.La_index_ne_zero cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁⟩⟩
  · have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    apply le_antisymm
    · intro v hv
      exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
    · intro v hv y hy
      obtain ⟨a, b, -, hab⟩ := hI v hv y hy
      refine ⟨b, ?_⟩
      show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
      rw [hab]; simp
  · intro x hx y hy
    have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    have hs := IO.semiChar_of_HfInt _ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im = (b : ℝ) := by rw [hab]; simp
    rw [hs]
    congr 1
    show Complex.exp (-((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ)))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ))
    rw [him]; exact (exp_pi_int b).symm

theorem laHyp_and_eSmooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  intro D X s cc δ B χ cD a b hX hs hcc hδ hV ha hb
  have hL := latAll B hcc hδ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hV a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hV a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.ThetaMove.LatticeFacts
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_all_sig : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  intro D hT h2 W P Q hW hs
  have hv : DefiniteVolumeEqMass D := mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
    (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    rw [← hrk]
    exact hv W hW (fun τ => by rw [hs τ, hrk]; rfl)
  · by_cases h2r : 2 ≤ P + Q
    · exact GlobalTheory.T.vol_eq_mass_selfDual_rank_ge_two D hT h2 hv W P Q hW hs h2r
    · have hP : P = 0 := by omega
      have hQ1 : Q = 1 := by omega
      subst hP hQ1
      have e1 : D.vol W = D.vol (GlobalTheory.NegSpace.neg W) :=
        GlobalTheory.T.volume_negativeDefinite_eq_opposite D hT W 1 hW hs
      have hN : (GlobalTheory.NegSpace.neg W).SigOK := GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW
      have e2 : D.vol (GlobalTheory.NegSpace.neg W) = massI D (GlobalTheory.NegSpace.neg W).rank :=
        hv _ hN (fun τ => by rw [GlobalTheory.NegSpace.neg_sig, hs τ, GlobalTheory.NegSpace.neg_rank, hrk])
      rw [e1, e2, GlobalTheory.NegSpace.neg_rank, hrk]

end GlobalTheory.Glob
end
