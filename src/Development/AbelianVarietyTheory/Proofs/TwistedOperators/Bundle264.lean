module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle249
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle248
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasProd_localTwistedLFactor_div_unitaryLocalFactor : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  first | exact @GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | exact GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | (intros; apply GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)

    rw [map_add (f := _), map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add (f := _), add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.MoverStd

theorem exists_mul_std : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  intro D S k₀ Λ' σ w hσ hk hm v hv
  obtain ⟨hfg, -, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    exact (Pi.basisFun_apply D.host.E (Fin S.rank) i).symm
  have ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u :=
    fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by
      by_cases hv' : w.asIdeal ≤ v'.asIdeal
      · have e : v' = w := (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm
        subst e
        refine Or.inr fun ε hε i j => ?_
        obtain ⟨α, rfl, -, hα0⟩ := hε
        have hασ : α * σ = 0 := by
          refine FiniteAdeleRing.ext D.host.F fun u => ?_
          change α u * σ u = 0
          by_cases hu : u = v'
          · subst hu
            rw [show σ u = 0 from hσ, mul_zero]
          · rw [show α u = 0 from hα0 u hu, zero_mul]
        have hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α := by
          refine Prod.ext ?_ ?_
          · change (0 : Ainf D.host.F) * (1 - 0) = 0
            rw [zero_mul]
          · change α * (1 - σ) = α
            rw [mul_sub, mul_one, hασ, sub_zero]
        have h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0 := by
          rw [← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]
        have := congrArg (cA D) h0
        rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
        have e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
          change (pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1
          rw [map_one]
        have e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
            (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
          rw [Matrix.one_apply]
          split_ifs
          exacts [map_one _, map_zero _]
        rw [e1, e'] at this
        exact this
      · exact Or.inl (if_neg hv')) u
  obtain ⟨t, htw, H⟩ := MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by
      have h1 : ¬ v'.asIdeal ≤ w.asIdeal := fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
      exact ⟨a, ha', ha⟩)
    (L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs
    (fun z hz => by
      have hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E)) := AddSubgroup.closure_mono (by
        rintro y ⟨a, ha, x, hx, e⟩
        exact ⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz
      change MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _
      rw [← ht z]
      exact MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))
  exact ⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩

end GlobalTheory.Ker.MoverStd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.latticeTransport_congruence_of_frameVectors : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  first | exact @GlobalTheory.LevCong.cong_of_frame | exact GlobalTheory.LevCong.cong_of_frame | (intros; apply GlobalTheory.LevCong.cong_of_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mulVec_sub_mem_latticeCompletion_of_lattice : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)), (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  first | exact @GlobalTheory.LevExt.mulVec_sub_mem_hatV | exact GlobalTheory.LevExt.mulVec_sub_mem_hatV | (intros; apply GlobalTheory.LevExt.mulVec_sub_mem_hatV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (c : D.host.E), (∀ x ∈ L, c • x ∈ L') → ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c) • u ∈ hatV L' := by
  first | exact @GlobalTheory.LevkSmul.smul_mem_hatV | exact GlobalTheory.LevkSmul.smul_mem_hatV | (intros; apply GlobalTheory.LevkSmul.smul_mem_hatV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockPolynomialVector_injective_nonzeroVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  first | exact @GlobalTheory.FockPolyInj.fvec_injective | exact GlobalTheory.FockPolyInj.fvec_injective | (intros; apply GlobalTheory.FockPolyInj.fvec_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_group_congruent_of_two_lattice_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_two_moves | exact GlobalTheory.Ker.LevMove.levK_of_two_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_two_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LevMov.finE_mem_St_of_isMov | exact GlobalTheory.LevMov.finE_mem_St_of_isMov | (intros; apply GlobalTheory.LevMov.finE_mem_St_of_isMov <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def liftI (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal

theorem frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  unfold frMapAdj
  simp

theorem isIntM_zero {b a : ℕ} : IsIntM (0 : Matrix (Fin b) (Fin a) (EAf D)) := fun _ _ => zero_mem _

theorem redM_frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Formalism.L2.DIV.Pl D.host.E) : redM PP (frMapAdj S T βS βT 0) = 0 := by
  have h0 : IsIntM (frMapAdj S T βS βT 0) := by rw [frMapAdj_zero]; exact isIntM_zero
  have h := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT 0 0 h0 h0).2 PP
  rw [add_zero] at h
  exact (left_eq_add.mp h)

def liftL (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT x) = 0}
  zero_mem' := by
    refine ⟨fun i j => by simp, ?_, fun PP _ => ?_⟩
    · rw [frMapAdj_zero]; exact isIntM_zero
    · exact redM_frMapAdj_zero S T βS βT PP
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x y hx2 hy2
    refine ⟨fun i j => ?_, h1, fun PP hPP => ?_⟩
    · simp only [Matrix.add_apply, mul_add, hx1 i j, hy1 i j]
    · rw [h2, hx3 PP hPP, hy3 PP hPP, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
      unfold frMapAdj
      simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
    have hI : IsIntM (frMapAdj S T βS βT (-x)) := fun i j => by
      rw [hneg, Matrix.neg_apply]; exact neg_mem (hx2 i j)
    obtain ⟨-, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x (-x) hx2 hI
    refine ⟨fun i j => ?_, hI, fun PP hPP => ?_⟩
    · simp only [Matrix.neg_apply, mul_neg, hx1 i j]
    · have := h2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero, hx3 PP hPP, zero_add] at this
      exact this.symm

def adjA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul βS.val (frMapAdj S T βS βT x)

def IsMover (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e a : AE D)
    (k₀ : GA D S) : Prop :=
  k₀ ∈ GfC S ∧ (∀ x : WO S T, IsHalf (1 - e - cA D e) x → actO S T k₀ 1 x = x) ∧
    ∀ x : WO S T, IsHalf (cA D e) x →
      frMapAdj S T βS βT (actO S T k₀ 1 x) = adjA S T βS βT a x

def IsGen {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e a : AE D) : Prop :=
  ∀ x : WO S T, IsHalf (cA D e) x →
    (IsIntM (adjA S T βS βT a x) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) ∧
    ((IsIntM (adjA S T βS βT a x) ∧
      ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a x) = 0) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)))

end GlobalTheory.LiftLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

theorem _root_.GlobalTheory.T.gridParameter_regular_card_eq_rankFormula : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parD i j) ∧ ((GlobalTheory.Grid.grid D τ).parD i j).card = GlobalTheory.Grid.rkV D i j := by
  first | exact @GlobalTheory.GridParDCount.parD_regular_card | exact GlobalTheory.GridParDCount.parD_regular_card | (intros; apply GlobalTheory.GridParDCount.parD_regular_card <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conj_localTwistedLFactor_ratio_inert_eq_zetaSum : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  first | exact @GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert | exact GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert | (intros; apply GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert <;> assumption)
end
