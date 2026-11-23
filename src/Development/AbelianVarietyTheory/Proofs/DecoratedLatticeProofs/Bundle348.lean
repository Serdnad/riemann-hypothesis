module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitWeilChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (q : SplitPt D k) (hU : q.UnitAA) : q.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := GlobalTheory.SplitCharCond.exists_idem q
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = q.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := GlobalTheory.SplitCharCond.pr_int q (hU.1 _ hm).2.2
  rwa [map_mul, GlobalTheory.SplitCharCond.pr_pair_tmul q h, map_one, map_one, mul_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (q : SplitPt D k) (hU : q.UnitAA) : valuation k (q.pr (incA D D.host.xi0)) = 1 := by
  have h1 := (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitCharCond.xi_zero_projection_integral q hU)
  have h2 := (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hm : q.pr (incA D D.host.xi0) * q.pr (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  have h3 := congrArg (valuation k) hm
  rw [map_mul, map_one] at h3
  by_contra hne
  have hlt : valuation k (q.pr (incA D D.host.xi0)) < 1 := lt_of_le_of_ne h1 hne
  have : valuation k (q.pr (incA D D.host.xi0)) * valuation k (q.pr (incA D D.host.xi0⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitWeilChar

namespace GlobalTheory.SplitWeilChar

theorem weil_char_conductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  intro D k _ _ _ _ q ψ hψ hU
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  set u : k := q.pr (incA D D.host.xi0) with hu
  have hv : valuation k u = 1 := valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  let χ : AddChar k Circle := ψk.mulShift u⁻¹
  have hχ : q.IsChar ψ χ := by
    intro a
    have e1 : (χ a : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec (u⁻¹ * a)) := hk (u⁻¹ * a)
    have e2 := GlobalTheory.SplitCharCond.sec_mul_pr q (u⁻¹ * a) (incA D D.host.xi0)
    rw [← hu, show u⁻¹ * a * u = a by field_simp] at e2
    rw [e1, ← e2]
  have hc1 : HasConductor χ 1 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ χ hψ hχ hU
  have hcu : HasConductor χ (Units.mk0 u hu0) := by
    intro x
    rw [Units.val_mk0, hv]
    have := hc1 x
    rwa [Units.val_one, map_one] at this
  have he : ψk = χ.mulShift ((Units.mk0 u hu0 : kˣ) : k) := by
    ext x
    simp only [χ, AddChar.mulShift_apply, Units.val_mk0]
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  refine ⟨ψk, hk, ?_⟩
  rw [he]
  exact GlobalTheory.CollapseCompare.hasConductor_mulShift hcu

end GlobalTheory.SplitWeilChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one' : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem sec_mul' (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idlU_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul' q x y
  rw [h, sec_one'] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idlU (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idlU_mul q _ _ x.mul_inv, idlU_mul q _ _ x.inv_mul⟩

theorem continuous_idlU : Continuous (idlU q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem res_eq_locK {PP : Formalism.L2.DIV.Pl D.host.E} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hr : Formalism.IndefR.Links.IsRes H PP c) {a : D.host.E} (ha : IntAt PP a)
    (ha0 : a ≠ 0) (r : (Formalism.L2.DIV.kP PP)ˣ) (hra : (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a) :
    c r = H.locK PP (Units.mk0 a ha0) := by
  obtain ⟨r₀, s, hs, e⟩ := ha
  have hs0 : (algebraMap (𝓞 D.host.E) D.host.E s) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsp := Formalism.L2.Col.reduction_spec PP hs e
  have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
  have h2 := hr r₀ (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu * r) (by simp [e])
    (by simp [hra, hsp])
  rw [map_mul, map_mul, h1] at h2
  exact mul_left_cancel h2

end Place
end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem chi_idlU_rat {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle}
    {H : Formalism.L2.Host.HChar D.host.E} (hχ : Formalism.IndefR.Links.ChrEq χ H) {a : D.host.E} (ha0 : a ≠ 0) (u : kˣ)
    (hu : (u : k) = (ofSplit q).pr a) : (χ (idlU q u) : ℂ) = H.locK PP (Units.mk0 a ha0) := by
  exact hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idlU q u) (by
        change q.sec u + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hu]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)

end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)
section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

def prOU : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prOU_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prOU q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prOU q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prOU q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prOU_le {PP : Formalism.L2.DIV.Pl D.host.E} (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x)
    (z : 𝓞 D.host.E) : valuation k (prOU q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 ((hi _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

end Place

theorem tame_and_res : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  intro D k _ _ _ _ q PP h hi hd χ H c μ hχ hr hμ
  have comp : ∀ x : kˣ, (μ x : ℂ) = χ (idlU q x) := fun x => hμ x (idlU q x) rfl
  have val : ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), IntAt PP a →
      (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
    intro a u r ha hra hu
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA D)).map_zero)
    apply Units.ext
    rw [comp u, chi_idlU_rat q h hχ ha0 u hu, res_eq_locK hr ha ha0 r hra]
  refine ⟨?_, val⟩
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 →
      χ (idlU q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    have ha : IntAt PP a := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have hred : Formalism.L2.Col.redP PP a = 1 := by
      obtain ⟨r₀, s, hs, e⟩ := ha
      have hsp := Formalism.L2.Col.reduction_spec PP hs e
      have e' : prOU q s * y = prOU q r₀ := by
        rw [hy]
        exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
      have hrs : r₀ - s ∈ PP.asIdeal := by
        rw [prOU_lt q h, map_sub, ← e', ← mul_sub_one, map_mul]
        calc valuation k (prOU q s) * valuation k ((y : k) - 1) ≤ 1 * valuation k ((y : k) - 1) :=
              by gcongr; exact prOU_le q hi s
          _ < 1 := by rwa [one_mul]
      haveI := PP.isMaximal
      letI := Ideal.Quotient.field PP.asIdeal
      have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have e2 : Ideal.Quotient.mk PP.asIdeal r₀ = Ideal.Quotient.mk PP.asIdeal s :=
        Ideal.Quotient.eq.2 hrs
      rw [e2] at hsp
      exact mul_left_cancel₀ hu (hsp.trans (mul_one _).symm)
    have h1 := val a y 1 ha (by rw [Units.val_one, hred]) hy
    rw [map_one] at h1
    have h2 := comp y
    rw [h1, Units.val_one] at h2
    exact Circle.coe_injective h2.symm
  intro x hx
  suffices hs : χ (idlU q x) = 1 by
    apply Units.ext
    rw [comp x, hs]
    simp
  by_contra hne
  have hc : Continuous fun y => χ (idlU q y) := hχ.1.1.comp (continuous_idlU q)
  have h1 : {y : kˣ | χ (idlU q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

end GlobalTheory.LocMod.SplitHecke
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

end GlobalTheory.CoreFrameLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIntUp

theorem sec_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a b : k) : q.sec (a * b) = q.sec a * q.sec b := by

  have he : ∀ c : k, q.sec c = q.e * q.sec c := fun c => by rw [← q.sec_pr, q.pr_sec]
  have h1 : q.sec (a * b) = q.e * (q.sec a * q.sec b) := by
    rw [← q.sec_pr, map_mul q.pr, q.pr_sec, q.pr_sec]
  rw [h1, ← mul_assoc, ← he]

private lemma mulVec_sec_eq_sec_mulVec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {m n : Type} [Fintype n]
    (u : Matrix m n (AE D)) (z : n → k) :
    u *ᵥ (fun j => q.sec (z j)) = fun i => q.sec ((u.map q.pr *ᵥ z) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : q.sec (z j) = q.e * q.sec (z j) := by rw [← q.sec_pr, q.pr_sec]
  rw [sec_mul', q.sec_pr]
  conv_lhs => rw [he]
  ring

theorem exists_int_up : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hSd _ hS hT u hu hh
  refine ⟨(ofSplit q).down FS FT u, ?_, (GlobalTheory.LocMod.Witness.up_down (ofSplit q) FS FT hh).symm⟩
  intro r s

  have hz : (fun i => q.sec ((FS.β *ᵥ Pi.single s 1) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    refine (hS (Pi.single s 1)).1 fun i => ?_
    rcases eq_or_ne i s with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _

  have hmem := GlobalTheory.FinPl.LatMem.latO_maps hSd hu hz
  rw [hU.2 T LT, mulVec_sec_eq_sec_mulVec q u (FS.β *ᵥ Pi.single s 1)] at hmem

  have hcol : FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s) =
      (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr *ᵥ (FS.β *ᵥ Pi.single s 1) := by
    have e1 : (fun r => (ofSplit q).down FS FT u r s) = (ofSplit q).down FS FT u *ᵥ Pi.single s 1 := by
      funext r; simp [Matrix.mulVec_single]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [GlobalTheory.LocMod.Place.down, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rfl
  have hin : (fun i => q.sec ((FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s)) i)) ∈
      GlobalTheory.FinPl.latV T LT (· = q.v) := by
    rw [hcol]; exact hmem
  exact (hT _).2 hin r

end GlobalTheory.HalfIntUp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _


open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in

theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

theorem _root_.GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  first | exact @GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt | exact GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt | (intros; apply GlobalTheory.ThetaNormTwist.normSq_thetaLocalDatum_at_twistPlace_alt <;> assumption)
end
