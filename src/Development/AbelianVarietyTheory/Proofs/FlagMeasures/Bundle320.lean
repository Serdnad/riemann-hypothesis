module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle035
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitRes

open IsDedekindDomain

section Cast

variable {E : Type} [Field E] [NumberField E]

theorem tensCastR_comm_symm_tmul_one {F₁ F₂ : Subfield E} (h : F₁ = F₂) (y : E) :
    GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
      (y ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁))) = y ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂) := by
  subst h
  exact (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _

theorem tensCastR_comm_symm_one_tmul {F₁ F₂ : Subfield E} (h : F₁ = F₂) (c : FiniteAdeleRing (𝓞 F₁) F₁)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F₁) :
    ∃ c' : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, c' v ∈ v.adicCompletionIntegers F₂) ∧
      GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
        ((1 : E) ⊗ₜ[F₁] c)) = (1 : E) ⊗ₜ[F₂] c' := by
  subst h
  exact ⟨c, hc, (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _⟩

end Cast

def projE (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) :
    Formalism.IndefR.Lev.EAf D →+* s.v.adicCompletion (maximalRealSubfield D.host.E) :=
  s.proj.comp (GlobalTheory.FixedConj.adeleEquiv D hF).symm.toRingHom

theorem projE_apply (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (x : Formalism.IndefR.Lev.EAf D) :
    projE D hF s x = s.proj (GlobalTheory.StdFrame.tensCastR hF
      ((Algebra.TensorProduct.comm (↥D.host.F) (FiniteAdeleRing (𝓞 ↥D.host.F) ↥D.host.F) D.host.E).symm x)) := rfl

theorem projE_adeleEquiv (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (a : ReciprocityTheory.Aut.AL D.host.E) : projE D hF s (GlobalTheory.FixedConj.adeleEquiv D hF a) = s.proj a := by
  simp [projE]

theorem projE_tmul_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (y : D.host.E) : projE D hF s (y ⊗ₜ[↥D.host.F] (1 : Formalism.L2.Herm.Af ↥D.host.F)) = s.i y := by
  rw [projE_apply, tensCastR_comm_symm_tmul_one]
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem projE_le_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.IndefR.Lev.EAf D) (hz : z ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) : Valued.v (projE D hF s z) ≤ 1 := by
  have hle : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring.comap (projE D hF s) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, projE_tmul_one]
      exact s.split_le_one y
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      obtain ⟨c', hc', e⟩ := tensCastR_comm_symm_one_tmul hF c hc
      rw [projE_apply, e]
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hc' s.v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hle hz)

theorem projE_lt_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (hz : z ∈ Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) :
    Valued.v (projE D hF s (z : Formalism.IndefR.Lev.EAf D)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, projE_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    calc Valued.v (projE D hF s (c : Formalism.IndefR.Lev.EAf D)) * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D))
        ≤ 1 * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D)) := by
          gcongr
          exact projE_le_one D hF s _ c.2
      _ < 1 := by rwa [one_mul]

theorem resS_adeleEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  intro D hF s a ha m _hA hm
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩)
  have e1 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) ⟨_, ha⟩ :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := ↥D.host.F) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) (Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b) :=
    Ideal.quotientMap_mk
  have hmem : (⟨_, ha⟩ : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) - Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b ∈
      Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) < 1 := by
    have := projE_lt_one D hF s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, projE_tmul_one, projE_adeleEquiv] at this
  have h2 : b - (m : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    show Valued.v (s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)) < 1
    have e : s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) -
          (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, map_natCast, map_natCast]
      ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)
  rw [← hb, ← map_natCast (Ideal.Quotient.mk s.w.asIdeal) m, Ideal.Quotient.eq]
  exact h2

end GlobalTheory.SplitRes

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LiftInt

section Val

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def ltIdeal : Ideal v.integer where
  carrier := {x | v (x : K) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at *
    calc v (c : K) * v (x : K) ≤ 1 * v (x : K) := by gcongr; exact c.2
      _ < 1 := by rwa [one_mul]

theorem det_sub_lt {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1)
    (hB : ∀ i j, v (B i j) ≤ 1) (h : ∀ i j, v (A i j - B i j) < 1) : v (A.det - B.det) < 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨B i j, hB i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have eB : B0.map v.integer.subtype = B := by ext i j; rfl
  have hm : A0.map (Ideal.Quotient.mk (ltIdeal v)) = B0.map (Ideal.Quotient.mk (ltIdeal v)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq]
    exact h i j
  have hd := congrArg Matrix.det hm
  have d1 : Ideal.Quotient.mk (ltIdeal v) A0.det = (A0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  have d2 : Ideal.Quotient.mk (ltIdeal v) B0.det = (B0.map (Ideal.Quotient.mk (ltIdeal v))).det :=
    RingHom.map_det _ _
  rw [← d1, ← d2, Ideal.Quotient.eq] at hd
  have e1 : v.integer.subtype A0.det = (A0.map v.integer.subtype).det := RingHom.map_det _ _
  have e2 : v.integer.subtype B0.det = (B0.map v.integer.subtype).det := RingHom.map_det _ _
  rw [eA] at e1
  rw [eB] at e2
  have : v ((A0.det - B0.det : v.integer) : K) < 1 := hd
  rw [← e1, ← e2, ← map_sub]
  exact this

theorem adjugate_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    ∀ i j, v (A.adjugate i j) ≤ 1 := by
  let A0 : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have eA : A0.map v.integer.subtype = A := by ext i j; rfl
  have e : A0.adjugate.map v.integer.subtype = (A0.map v.integer.subtype).adjugate :=
    RingHom.map_adjugate _ _
  rw [eA] at e
  intro i j
  rw [← e]
  exact (A0.adjugate i j).2

end Val

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

theorem natCast_lt_one (s : SplitPlace L) (g : ℕ) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) :
    Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
  have h : Valued.v (s.i ((g : 𝓞 L) : L)) < 1 := hg
  simpa using h

theorem intCast_eq_one (s : SplitPlace L) (g : ℕ) (hp : g.Prime) (hg : ((g : 𝓞 L) ∈ s.w.asIdeal)) (m : ℤ)
    (hm : ¬ (g : ℤ) ∣ m) : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  have hcop : IsCoprime (g : ℤ) m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : ¬ g ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 h1
  obtain ⟨a, b, hab⟩ := hcop
  refine le_antisymm (intCast_le_one s m) (not_lt.mp fun hlt => ?_)
  have e : ((a : s.v.adicCompletion (maximalRealSubfield L))) * (g : s.v.adicCompletion (maximalRealSubfield L)) +
      (b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : s.v.adicCompletion (maximalRealSubfield L))) hab
  have h1 : Valued.v ((a : s.v.adicCompletion (maximalRealSubfield L)) * (g : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((g : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s a
      _ < 1 := by rw [one_mul]; exact natCast_lt_one s g hg
  have h2 : Valued.v ((b : s.v.adicCompletion (maximalRealSubfield L)) * (m : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) := by gcongr; exact intCast_le_one s b
      _ < 1 := by rwa [one_mul]
  have h3 := lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 h2)
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

end Place

theorem mem_Umax_of_isLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  intro L _ _ _ n s g hp hg x γ hx
  obtain ⟨htriv, hred⟩ := hx
  haveI : Fact g.Prime := ⟨hp⟩
  set A : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) with hAdef
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
  let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    M.map (Int.castRingHom _)
  have hB : ∀ i j, Valued.v (B i j) ≤ 1 := fun i j => intCast_le_one s _
  have hAB : ∀ i j, Valued.v (A i j - B i j) < 1 := by
    intro i j
    have := hred i j
    have e : B i j = ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) :
        s.v.adicCompletion (maximalRealSubfield L)) := by
      change (((M i j : ℤ)) : s.v.adicCompletion (maximalRealSubfield L)) = _
      exact Int.cast_natCast _
    rw [e]
    exact this
  have hA : ∀ i j, Valued.v (A i j) ≤ 1 := by
    intro i j
    have e : A i j = (A i j - B i j) + B i j := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (hAB i j).le (hB i j))
  have hdetB : B.det = ((M.det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) M).symm
  have hMγ : M.map (Int.castRingHom (ZMod g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext i j
    change (((M i j : ℤ)) : ZMod g) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdetM : ((M.det : ℤ) : ZMod g) = (γ : Matrix (Fin n) (Fin n) (ZMod g)).det := by
    rw [← hMγ]
    exact RingHom.map_det (Int.castRingHom (ZMod g)) M
  have hne : ¬ (g : ℤ) ∣ M.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hdetM]
    exact (Matrix.isUnits_det_units γ).ne_zero
  have hvB : Valued.v B.det = 1 := by rw [hdetB]; exact intCast_eq_one s g hp hg _ hne
  have hvA : Valued.v A.det = 1 := by
    have hd := det_sub_lt Valued.v A B hA hB hAB
    have e : A.det = (A.det - B.det) + B.det := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hvB]; exact hd), hvB]
  apply GlobalTheory.TSetFin.mem_Umax_of_loc s x htriv hA
  intro i j
  rw [map_inv, Matrix.coe_units_inv, ← hAdef, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul,
    Ring.inverse_eq_inv', map_inv₀, hvA, inv_one, one_mul]
  exact adjugate_le_one Valued.v A hA i j

end GlobalTheory.LiftInt
end
end

section

noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem crd_map_mulVec (m : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (m y) = (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i) *ᵥ X.crd y := by
  unfold Formalism.L2.SG.Pf.toV HidaSetting.crd crdOf
  have hb : ∀ j : Fin X.B.I.n, (∑ i, X.ιE ((Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) i) • X.bas i) = X.bas j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_apply, hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hb]
  funext i
  conv_lhs => rw [← X.bas.sum_repr y]

  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
  Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phiV_linMat (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V) :
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  obtain ⟨-, hQ, -⟩ := C.isT τ
  refine ⟨C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ *
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *
      X.B.I.P (vOf X τ) * C.Q τ, fun y => ?_⟩
  have hP : (X.B.I.P (vOf X τ))⁻¹ * ((Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) * (X.B.I.P (vOf X τ) * (X.B.I.P (vOf X τ))⁻¹)) =
      (X.B.I.P (vOf X τ))⁻¹ * (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) := by
    by_cases h : IsUnit (X.B.I.P (vOf X τ)).det
    · rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul, Matrix.zero_mul]
  have hw : (fun i => X.B.I.φ (vOf X τ) (X.crd (m y) i)) =
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *ᵥ
        (fun i => X.B.I.φ (vOf X τ) (X.crd y i)) := by
    rw [crd_map_mulVec m y]
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e1 : ∀ z, GlobalTheory.TypeAsm.phiV C τ z =
      (C.Qi τ * (X.B.I.P (vOf X τ))⁻¹) *ᵥ (fun i => X.B.I.φ (vOf X τ) (X.crd z i)) := by
    intro z
    unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.HidaSetting.rv
    rw [Matrix.mulVec_mulVec]
  rw [e1, e1, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, hP]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

theorem phiV_linMat_all : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau)
    (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  intro D X C τ m
  exact GramPf.phiV_linMat C τ m

end GlobalTheory.TypeAsm
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NonzeroDefect

theorem num_first (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) :
    2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 1)) ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have h1 : q ^ (-((k : ℤ) - 1)) ≤ q ^ (-((k : ℤ) - 2 * r - 5)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have hq0 : 0 < q := by linarith
  gcongr
  norm_num

theorem num_second (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) (hk : 4 * r + 7 ≤ k) :
    98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) *
        (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤ q ^ (-((k : ℤ) - 2 * r - 5)) := by
    rw [← zpow_natCast, ← zpow_mul]
    exact zpow_le_zpow_right₀ (by linarith) (by push_cast; omega)
  gcongr

theorem nonzeroDefect_height_power_absorbs_constants (H : ℝ) (hH : 2 ≤ H) (r : ℕ) :
    H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1)))) ≤
      H ^ (39 * (r + 1) ^ 2) := by
  have h0 : 0 < H := by linarith
  have h9 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by gcongr
  calc H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))))
      = 392 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by ring
    _ ≤ H ^ 9 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by gcongr
    _ = H ^ (9 + (2 * (r + 2) + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1))) := by
        simp only [pow_add H]
    _ ≤ H ^ (39 * (r + 1) ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.zero_le r])

theorem ampSq_nonzero_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ
  · obtain ⟨d, Λ, hT, hB⟩ := hex
    have hq : (2 : ℝ) ≤ (S.q : ℝ) := by
      have := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
      exact_mod_cast this
    have hqH : (S.q : ℝ) ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.1 hB
    have hH : (2 : ℝ) ≤ S.Hp := hq.trans hqH
    have hH0 : (0 : ℝ) ≤ S.Hp := by linarith
    have hq0 : (0 : ℝ) < (S.q : ℝ) := by linarith
    have key := GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz L r k S hk
      (ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) *
        (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn)
      (fun β => (GlobalTheory.T.hermitianFrames_firstType_ampSq_bound L r k S hk β).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_first _ _ hq hH0 r k)) _))
      (fun β J βJ => (GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le L r k S hk β J βJ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_second _ _ hq hH0 r k hk)) _))
    refine key.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (nonzeroDefect_height_power_absorbs_constants _ hH r) (by positivity)
  · have h0 : (S.ampSq fun d Λ => ¬ S.BBzero d Λ) = 0 := by
      have ha : ∀ d, S.amp d (fun Λ => ¬ S.BBzero d Λ) = 0 := by
        intro d
        unfold Frames.amp
        have : ∀ Λ, ¬ (S.IsTerm d Λ ∧ ¬ S.BBzero d Λ) := fun Λ h => hex ⟨d, Λ, h⟩
        simp only [this, if_false, tsum_zero]
      unfold Frames.ampSq Frames.sumData
      simp [ha]
    rw [h0]
    exact zero_le

end GlobalTheory.HL.NonzeroDefect
end
