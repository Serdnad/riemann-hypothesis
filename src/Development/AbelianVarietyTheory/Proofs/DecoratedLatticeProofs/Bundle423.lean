module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle369
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  first | exact @GlobalTheory.QPl.LastTwo.entries_mem_SB | exact GlobalTheory.QPl.LastTwo.entries_mem_SB | (intros; apply GlobalTheory.QPl.LastTwo.entries_mem_SB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.IdVGen

open GlobalTheory.SemiLocalFrame

theorem exists_gen_semiLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      b⁻¹ * z ∈ semiLoc E v := by
  have hfg : (Submodule.span (semiLoc E v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG := by
    obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal
    (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc E v)⁰ E)).principal
  have hb' : ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      ∃ a : semiLoc E v, a • b = z := fun z => by
    rw [← Submodule.mem_span_singleton, ← hb]
    exact (mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)
    obtain ⟨a, ha⟩ := (hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩
    rw [← ha, smul_zero]
  refine ⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩
  · rintro ⟨a, rfl⟩
    have : b⁻¹ * (a • b) = a := by
      change b⁻¹ * ((a : E) * b) = a
      field_simp
    rw [this]; exact a.2
  · change b⁻¹ * z * b = z
    field_simp

theorem exists_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ (∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) * b ∈ 𝔟) ∧
      ∀ c ∈ 𝔟, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ o : 𝓞 E,
        algebraMap F E (t : F) * (b⁻¹ * c) = algebraMap (𝓞 E) E o := by
  obtain ⟨b, hb0, hb⟩ := exists_gen_semiLoc v h𝔟
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  refine ⟨b, hb0, ?_, fun c hc => ?_⟩
  · obtain ⟨t, ht, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    exact ⟨t, ht, by rw [← smul_eq]; exact h⟩
  · have h1 := (hb c).1 ⟨1, hone, by rw [map_one, one_smul]; exact hc⟩
    obtain ⟨t, ht, h⟩ := exists_of_mem_semiLoc v h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    exact ⟨t, ht, o, by rw [← smul_eq, ho]⟩

variable {D : D7}

theorem inv_mem_integers {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (t : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation D.host.F (t : D.host.F) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K := D.host.F)).2 hv
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : D.host.F)⁻¹)
  have h3 : v.valuation D.host.F (t : D.host.F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem smul_inv_mem {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (t : D.host.F)⁻¹ • α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w ((t : D.host.F)⁻¹ • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => by rw [map_smul, h0 w hw, smul_zero]⟩
  by_cases hw : w = v
  · subst hw
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (inv_mem_integers hv) (hα w)
  · rw [map_smul, h0 w hw, smul_zero]
    exact zero_mem _

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  have : c • pairA F 0 α = ((c • (0 : Ainf F), c • α) : Ainf F × Af F) := rfl
  rw [this, smul_zero]; rfl

theorem tmul_eq_of_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : F) (hc : c ≠ 0)
    (α : Af F) (z : E) : pairA F 0 α ⊗ₜ[F] z = pairA F 0 (c⁻¹ • α) ⊗ₜ[F] (algebraMap F E c * z) := by
  rw [pairA_smul, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem tmul_eq {v : Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal) (α : Af D.host.F) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z =
      pairA D.host.F 0 ((t : D.host.F)⁻¹ • α) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) * z) := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  exact tmul_eq_of_ne _ hF α z

theorem gen_mem_idAt {v : Pl D} {α : Af D.host.F} (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z ∈ idAt D (· = v) := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
  refine ⟨?_, fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] z = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show evalV D.host.F w.1 α ⊗ₜ[D.host.F] z = 0
    rw [h0 w.1 w.2, TensorProduct.zero_tmul]

theorem gen_mem_intAt {v : Pl D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E o ∈ intAt D (· = v) :=
  ⟨gen_mem_idAt h0 _, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩

theorem intAt_zero' (v : Pl D) : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (finPart D) a b]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg (finPart D) a]; exact neg_mem ha.2⟩

theorem incA_mul_tmul (y : AF D.host.F) (e z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem idV_gen : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧
    ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, ⟨t₀, ht₀, hx𝔞⟩, hc⟩ := exists_gen v h𝔞
  refine ⟨x, hx0, fun s => ⟨fun hs => ?_, fun ⟨h1, _⟩ => ?_⟩⟩
  · unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
      obtain ⟨t, ht, o, ho⟩ := hc c hc'
      obtain ⟨h1, h2⟩ := smul_inv_mem ht hα h0
      refine ⟨?_, gen_mem_idAt h0 c⟩
      rw [incA_mul_tmul, tmul_eq ht α (x⁻¹ * c), ho]
      exact gen_mem_intAt h1 h2 o
    | zero => exact ⟨by rw [mul_zero]; exact intAt_zero' v, zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨by rw [mul_add]; exact intAt_add' ha.1 hb.1, add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by rw [mul_neg]; exact intAt_neg' ha.1, neg_mem ha.2⟩
  · have h3 : incA D x⁻¹ * s ∈ idV (1 : FI D) v := (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 h1
    have key : ∀ y ∈ idV (1 : FI D) v, incA D x * y ∈ idV 𝔞 v := by
      intro y hy
      unfold idV at hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc'
        obtain ⟨h1', h2'⟩ := smul_inv_mem ht₀ hα h0
        apply AddSubgroup.subset_closure
        refine ⟨_, h1', h2', algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o),
          ?_, ?_⟩
        · have := (𝔞 : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx𝔞
          rw [Algebra.smul_def] at this
          have e : algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o) =
              algebraMap (𝓞 D.host.E) D.host.E o * (algebraMap D.host.F D.host.E (t₀ : D.host.F) * x) := by ring
          rw [e]; exact this
        · rw [incA_mul_tmul, tmul_eq ht₀ α]
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul] at this

end GlobalTheory.IdVGen

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftModel

theorem isSelfDualC_lineLat : ∀ (D : D7) (S : HSp D) (ζ : Fin S.rank → D.host.E), IsLineVec S ζ → ∀ (𝔄 : FI D), (∀ d : D.host.E, d ∈ 𝔄 ↔ ∀ c ∈ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ)) → IsSelfDualC S (GlobalTheory.SeeSaw.LiftModel.lineLat S ζ 𝔄) := by
  intro D S ζ hζ 𝔄 h𝔄
  classical
  obtain ⟨h1, hH⟩ := hζ
  haveI : Subsingleton (Fin S.rank) := by rw [h1]; infer_instance
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  have all : ∀ i : Fin S.rank, i = i₀ := fun i => Subsingleton.elim _ _
  set z := ζ i₀ with hz
  set g := S.gram i₀ i₀ with hg
  have eH : star ζ ⬝ᵥ S.gram *ᵥ ζ = star z * (g * z) := by
    simp only [dotProduct, mulVec, Fintype.sum_subsingleton _ i₀, Pi.star_apply]
    rfl
  have z0 : z ≠ 0 := by
    intro h0; apply hH; rw [eH, h0]; simp
  have repr : ∀ y : Fin S.rank → D.host.E, y = (y i₀ / z) • ζ := by
    intro y; funext i; rw [all i]; simp [div_mul_cancel₀ _ z0, ← hz]
  have memΛ : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ ∃ c ∈ 𝔄, c • ζ = y := by
    intro y
    simp [lineLat, Submodule.mem_map, LinearMap.toSpanSingleton_apply]
  have memΛ' : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ y i₀ / z ∈ 𝔄 := by
    intro y
    rw [memΛ]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [← hz, mul_div_cancel_right₀ _ z0] using hc
    · intro h
      exact ⟨_, h, (repr y).symm⟩
  have sum_eq : ∀ c d : D.host.E, ∑ i, ∑ j, star ((c • ζ) i) * S.gram i j * (d • ζ) j =
      star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ) := by
    intro c d
    rw [eH]
    simp only [Fintype.sum_subsingleton _ i₀, Pi.smul_apply, smul_eq_mul, star_mul', ← hz, ← hg]
    ring
  have dual : ∀ y : Fin S.rank → D.host.E, y ∈ lineLat S ζ 𝔄 ↔
      ∀ x ∈ lineLat S ζ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    rw [memΛ', h𝔄]
    constructor
    · intro h x hx
      obtain ⟨c, hc, rfl⟩ := (memΛ x).1 hx
      obtain ⟨b, hb⟩ := h c hc
      refine ⟨b, ?_⟩
      conv_rhs => rw [repr y]
      rw [sum_eq, hb]
    · intro h c hc
      obtain ⟨b, hb⟩ := h (c • ζ) ((memΛ _).2 ⟨c, hc, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb]
      conv_lhs => rw [repr y]
      rw [sum_eq]
  refine ⟨⟨?_, ?_⟩, dual⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔄).map _
  · obtain ⟨c, hc, hc0⟩ : ∃ c ∈ 𝔄, c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1m : (1 : D.host.E) ∈ 𝔄 := by
        rw [h𝔄]
        intro c hc
        exact ⟨0, by simp [hcon c hc]⟩
      exact one_ne_zero (hcon 1 h1m)
    have hcζ : c • ζ ∈ lineLat S ζ 𝔄 := (memΛ _).2 ⟨c, hc, rfl⟩
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SeeSaw.LiftModel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepLevLaw

theorem omegaQ_empty {D : D7} {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (fun PP hP => absurd hP (Finset.notMem_empty PP))]
  simp



open Classical in
theorem stepLevLaw : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → ∀ ω, IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω → ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → ∀ κ ∈ levS s.V s.β s.L, κ ∈ GfC s.V ∧ ω (κ, 1) f = Lev.levChi s.V s.β s.L κ • f := by
  intro D c hc k s s' hs hs' ω hW ξ f₀ f hv κ hκ
  refine ⟨hκ.1, ?_⟩
  have hPg : s.L.Pg = c.Pg := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← hPg, ← Finset.union_empty s.L.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k k.isLt
  have hlev : Lev.finE s.V κ ∈ lev D.sp.cm s.V.gram s.β s.L := hκ.2
  have sg : Lev.finE s.V κ ∈ St s.β := parLev_St hlev.1
  have sh : Lev.finE s'.V 1 ∈ St s'.β := by rw [map_one]; exact Subgroup.one_mem _
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
    hs.selfDual hs'.selfDual hs.frame hs'.frame hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hκ.1 (Subgroup.one_mem _) sg sh
  set G : ∀ PP : Pl D.host.E, GL (Fin s.V.rank) (kP PP) := fun PP => redFn s.β PP (Lev.finE s.V κ) with hG
  have h1' : ω (κ, 1) f₀ = ((∏ PP ∈ c.Pg, c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_inv, mul_one, hG]
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D s.V.rank s'.V.rank s.L (c.chi (↑k + 1)) G (fun PP hP => parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame κ 1 sg sh) _
    ((s.L.P.chi ⟨_, hlev.2⟩ * (∏ PP ∈ s.L.Pg, ∏ i ∈ Finset.range s.L.s, s.L.cg (i + 1) PP (dBlk (blkOf s.L.r s.L.t) (i + 1) (G PP))) *
      ∏ PP ∈ s.L.Pg, (c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β κ 1 sg sh x
      have i0 : IsHalf e (actO s.V s'.V κ⁻¹ 1⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), omegaQ_empty, omegaQ_empty, mul_one, mul_one]
        simp only [map_one, redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        exact hoG (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2]
  congr 1
  unfold Lev.levChi levFn
  rw [hQ, Finset.prod_empty, mul_one, extendOne_of_mem _ hlev.2, ← Units.val_mul, ← hPg, Finset.prod_inv_distrib]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.ChainOnto.StepLevLaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.VacTheta

theorem isFinComb_of_combAt {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ}
    (h : GlobalTheory.FinPl.CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this

end GlobalTheory.Fam.VacTheta

end
end
