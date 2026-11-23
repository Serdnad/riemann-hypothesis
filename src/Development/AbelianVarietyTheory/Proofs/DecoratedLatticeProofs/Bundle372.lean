module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle331
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_ofSplit (q : SplitPt D k) (x : D.host.E) : (ofSplit q).pr x = q.pr (incA D x) := rfl

theorem eq_sec_add_cA (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  rw [q.sec_pr, q.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff q a).1 ha]

theorem pr_mem_of_int (q : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : q.pr a ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt q).2 ha

theorem mem_intAt_iff_pr (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_int q h.2, pr_mem_of_int q ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add_cA q ha, RingHom.map_add (f := _)]
  exact add_mem ((q.int_iff _).1 h.1) ((cA_int_iff _).2 ((q.int_iff _).1 h.2))

theorem single_int {Y' : Type} [DecidableEq Y'] (m₁ : Y') (i : Y') : (Pi.single m₁ (1 : k) : Y' → k) i ∈ 𝒪[k] := by
  by_cases hi : i = m₁
  · subst hi; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem wpart {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E} {c : k} {m₀ : Y}
    (hI : IntIn q S F L) (hc : valuation k c = 1) (hu : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) (x : k) :
    (fun r => q.sec (x * (ofSplit q).pr (u r))) ∈ latV S L (· = q.v) ↔ x ∈ 𝒪[k] := by
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact zero_ne_one hc
  have e : (fun r => q.sec (x * (ofSplit q).pr (u r))) =
      fun r => q.sec ((F.β *ᵥ Pi.single m₀ (x / c)) r) := by
    funext r
    congr 1
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single m₀ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, ← hu r]
    field_simp
  rw [e, ← hI (Pi.single m₀ (x / c))]
  constructor
  · intro h
    have h1 := h m₀
    rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one] at h1
    exact (Valuation.mem_integer_iff _ _).2 h1
  · intro h i
    by_cases hi : i = m₀
    · subst hi
      rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one]
      exact (Valuation.mem_integer_iff _ _).1 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

theorem wbar {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E}
    (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hb : ∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k])
    (hb1 : ∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) (A : k) :
    (fun r => cA D (q.sec (A * (ofSplit q).pr (star (u r))))) ∈ latV S L (· = q.v) ↔ A ∈ 𝒪[k] := by
  have ht : ∀ i, (ofSplit q).pr (star ((S.gram *ᵥ u) i)) =
      ∑ j, q.pr (cA D (incA D (S.gram i j))) * (ofSplit q).pr (star (u j)) := by
    intro i

    simp only [pr_ofSplit, Matrix.mulVec, dotProduct, star_sum, star_mul', map_sum, map_mul, cA_incA]
  have hsum : ∀ x : Fin S.rank → k,
      ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
      A * ∑ m, (F.γ *ᵥ x) m * ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) := by
    intro x
    have h1 : ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
        A * ∑ i, x i * (ofSplit q).pr (star ((S.gram *ᵥ u) i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    congr 1
    have hx : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    generalize F.γ *ᵥ x = y at hx ⊢
    subst hx
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_)
    ring
  rw [csec_mem_iff hL]
  simp only [hsum]
  obtain ⟨m₁, hm₁⟩ := hb1
  constructor
  · intro h
    have hx : (fun i => q.sec ((F.β *ᵥ Pi.single m₁ (1 : k)) i)) ∈ latV S L (· = q.v) :=
      (hI _).1 (single_int (k := k) m₁)
    have h2 := h _ hx
    rw [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec,
      Finset.sum_eq_single m₁ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
      Valuation.mem_integer_iff, map_mul, hm₁, mul_one] at h2
    exact (Valuation.mem_integer_iff _ _).2 h2
  · intro hA x hx
    have hy := (hI (F.γ *ᵥ x)).2 (by rwa [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec])
    exact mul_mem hA (sum_mem fun m _ => mul_mem (hy m) (hb m))

theorem line_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (c : k) (m₀ : Y),
    IsSelfDualC S L → IntIn q S F L → valuation k c = 1 → (∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) →
    (∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k]) →
    (∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) →
    ∀ a ∈ GlobalTheory.FinPl.idAt D (· = q.v),
      ((fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S L Y _ _ F u c m₀ hL hI hc hu hb hb1 a ha
  have hy : (fun r => a * incA D (u r)) = (fun r => q.sec (q.pr a * (ofSplit q).pr (u r))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * (ofSplit q).pr (star (u r))))) := by
    funext r
    rw [Pi.add_apply]
    conv_lhs => rw [eq_sec_add_cA q ha]
    rw [add_mul, sec_mul_right]
    congr 1
    have e : incA D (u r) = cA D (incA D (star (u r))) := by rw [cA_incA, star_star]
    rw [e, ← RingHom.map_mul, sec_mul_right]
    rfl
  rw [hy]
  refine (decomp hL (fun r => q.pr a * (ofSplit q).pr (u r))
    (fun r => q.pr (cA D a) * (ofSplit q).pr (star (u r)))).trans ?_
  rw [mem_intAt_iff_pr q ha]
  exact and_congr (wpart hI hc hu _) (wbar hL hI hb hb1 _)

end GlobalTheory.SplitLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.SepProd

variable {D : D7}

theorem list_ofFn_prod_eq {M : Type*} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn fun j : Fin n => f j.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun j => h _ (Fin.succ_ne_zero j))
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_ofFn_prod_eq (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem mem_grpOff_of_suppAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {v : GlobalTheory.FinPl.Pl D} (hv : p.v ≠ v) :
    g ∈ grpOff V (· = v) := by
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idOff D (· = v))) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  have hmem : Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ idAt D (· = p.v) := by
    have := hg i j
    rw [Matrix.sub_apply] at this
    rw [← this]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt p)
  have h2 := (Ideal.mem_inf.1 hmem).2
  rw [Ideal.mem_iInf] at h2
  rw [idOff, Ideal.mem_iInf]
  rintro ⟨w, rfl⟩
  exact h2 ⟨w, fun e => hv e.symm⟩

end GlobalTheory.SeeSaw.SepProd


open GlobalTheory.SeeSaw.SepProd in
theorem GlobalTheory.SeeSaw.SepProd.prod_sep : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  intro D c v n G hG j' xs hxs i
  refine ⟨(xs i)⁻¹ * (List.ofFn xs).prod, ?_, by rw [mul_inv_cancel_left]⟩
  have hoff : ∀ i', i' ≠ i → xs i' ∈ grpOff (c.V j') (· = (G i).q.v) := fun i' hi' =>
    mem_grpOff_of_suppAt (G i').q (hxs i') fun e => hi' (hG.inj e)
  rw [grpOff, congGrp, MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_ofFn,
    list_ofFn_prod_eq (_ ∘ xs) i fun j hj => MonoidHom.mem_ker.1 (hoff j hj), Function.comp_apply, inv_mul_cancel]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.LevelCut

open GlobalTheory.SplitCut

variable {D : D7}

theorem entry_idAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2


open GlobalTheory.LocWeil.PlaceIdem in
theorem sum_act {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v)
    (y : AE D) (hy : y ∈ idAt D (fun u => u ∈ Set.range v)) :
    (1 - ∑ w, algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w))) * y = 0 := by
  unfold idAt at hy
  obtain ⟨h1, h2⟩ := hy
  have h1' : infPart D y = 0 := h1
  have h2' : ∀ u, u ∉ Set.range v → compAt D u y = 0 := fun u hu => by
    have := (Ideal.mem_iInf.1 h2) ⟨u, hu⟩
    exact (RingHom.mem_ker).mp this
  have h3 := key v hv y h2'
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 0 := by
    rw [finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  have h4 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 :=
    GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h1', mul_zero, RingHom.map_zero])
      (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero])

  rw [map_sub, map_sub, map_one, map_sum] at h3
  linear_combination h3 + h4

theorem pr_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    q.pr (q.e + cA D q.e) = 1 := by
  have h2 := q.split.2.1
  have ho : q.sec 1 = q.e := by rw [← q.pr.map_one, q.sec_pr, mul_one]
  have p1 : q.pr q.e = 1 := by rw [← ho, q.pr_sec]
  have p2 : q.pr (cA D q.e) = 0 := by rw [← one_mul (q.pr _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  rw [RingHom.map_add (f := _), p1, p2, add_zero]

theorem exists_coord {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (A B : Matrix (Fin N) (Fin N) k) (h1 : A * B = 1) (h2 : B * A = 1) : ∃ x : GL Y k, A = F.β * x.val * F.γ := by
  have key : ∀ A B : Matrix (Fin N) (Fin N) k, A * B = 1 → (F.γ * A * F.β) * (F.γ * B * F.β) = 1 := fun A B h => by
    calc (F.γ * A * F.β) * (F.γ * B * F.β) = F.γ * (A * (F.β * F.γ) * B) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h, Matrix.mul_one, F.γβ]
  refine ⟨⟨F.γ * A * F.β, F.γ * B * F.β, key A B h1, key B A h2⟩, ?_⟩
  calc A = (F.β * F.γ) * A * (F.β * F.γ) := by rw [F.βγ, Matrix.mul_one, Matrix.one_mul]
    _ = F.β * (F.γ * A * F.β) * F.γ := by simp only [Matrix.mul_assoc]


open GlobalTheory.LocWeil.PlaceIdem in
theorem exists_parts (V : HSp D) {n : ℕ} (v : Fin n → Pl D) (e : Fin n → AE D) (hv : Function.Injective v)
    (he : ∀ w, ∃ ε, IsPlaceIdem D (v w) ε ∧ e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε)
    (g : GA D V) (hg : g ∈ grpAt V (fun u => u ∈ Set.range v)) :
    ∃ h : Fin n → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w, mt V (h w) = (e w + cA D (e w)) • mt V g + (1 - (e w + cA D (e w))) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      g = ((List.finRange n).map h).prod := by
  set E : Fin n → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hE w, hh w]
  · apply GlobalTheory.SplitCut.mt_injective
    rw [mt_list_prod V h E _ hh hEo _ (List.nodup_finRange n), ← Fin.sum_univ_def]
    exact exists_widePullback_of_iteratedLine _ _ fun i j => sum_act v hv _ (entry_idAt V _ g hg i j)

theorem prod_local_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G →
    ∀ (j : ℕ) (k : GA D (c.V j)), k ∈ grpAt (c.V j) (· ∈ v.gP) → ∃ h : Fin n → GA D (c.V j),
      (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
        k = ((List.finRange n).map h).prod := by
  intro D c v n G hG j g hg
  have hP : (fun u => u ∈ v.gP) = fun u => u ∈ Set.range (fun i => (G i).q.v) := by
    funext u
    rw [hG.places u]
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [hP] at hg
  obtain ⟨h, h1, h2, h3⟩ := exists_parts (c.V j) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj
    (fun i => (G i).q.above) g hg
  refine ⟨h, fun i b hb => ?_, h3⟩
  have hm : ∀ a a' : GA D (c.V j), a * a' = 1 →
      (mt (c.V j) a).map (G i).q.pr * (mt (c.V j) a').map (G i).q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  obtain ⟨x, hx⟩ := exists_coord ((G i).FY j b hb) _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))
  refine ⟨x, hx, h1 i, ?_⟩
  change (mt (c.V j) (h i)).map (G i).q.pr = _
  rw [h2 i, GlobalTheory.GfCut.map_idem, pr_sum, one_smul, sub_self, zero_smul, add_zero]
  exact hx

end GlobalTheory.LevelCut
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.LocComp

theorem combAt_o {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (l : GlobalTheory.SeeSaw.LocPl ψ S T M M') {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P l.q.v) : GlobalTheory.FinPl.CombAt P l.o :=
  fun x hx i j => GlobalTheory.LocMod.PinInhab.mem_idAt_of_supp l.q hP (l.o_at x hx i j)

theorem combAt_comp {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {P : GlobalTheory.FinPl.Pl D → Prop} {e e' : WO S T →₀ ℂ} (he : GlobalTheory.FinPl.CombAt P e) (he' : GlobalTheory.FinPl.CombAt P e') :
    ∃ e'', GlobalTheory.FinPl.CombAt P e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f) := by
  have h4 := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.2.2.1
  have hm : ∀ {c : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt P c → GlobalTheory.FinPl.CombAt (fun p => P p ∨ False) c :=
    fun hc x hx i j => by simpa only [or_false] using hc x hx i j
  obtain ⟨e'', h1, h2⟩ := h4 e e' (hm he) (hm he')
  exact ⟨e'', fun x hx i j => by simpa only [or_false] using h1 x hx i j, h2⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  intro D ψ hψ S T M M' _ _ n
  induction n with
  | zero =>
    intro L _ P _
    refine ⟨Finsupp.single 0 1, GlobalTheory.FinPl.OffTest.combAt_single_zero P 1, fun F => ?_⟩
    rw [GlobalTheory.FinPl.OffTest.comb_single_zero]
    simp
  | succ n ih =>
    intro L hinj P hP
    obtain ⟨o₁, h₁, h₁'⟩ := ih (fun i => L i.succ) (fun a b h => Fin.succ_injective _ (hinj h)) P (fun i => hP i.succ)
    obtain ⟨o', h', h''⟩ := combAt_comp hψ (combAt_o (L 0) (hP 0)) h₁
    refine ⟨o', h', fun F => ?_⟩
    rw [h'', h₁', List.finRange_succ, List.foldr_cons, List.foldr_map]

end GlobalTheory.LocComp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.JacCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ J n _ _ c s hh F₀ F hF i
  obtain ⟨hc, h0, h1, h2⟩ := hF
  subst hc
  have hpr : ∀ a, p.pr a = Witness.prH p a := fun _ => rfl

  have hG : (J.W.gram)ᴴ = J.W.gram := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star J.W b a

  have L : ∀ {Z : Type} [Fintype Z] (M : Matrix (Fin J.W.rank) Z k) (z : Z),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * M r' z =
        (((J.d.eᴴ * J.W.gram).map (Witness.prH p)) * M) i z := by
    intro Z _ M z
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r' _ => ?_

    rw [← Finset.sum_mul, Matrix.map_apply, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, hpr, hpr]
  have Ls : ∀ (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ) (t : k),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * (t * p.pr (M r' j)) =
        t * Witness.prH p ((J.d.eᴴ * J.W.gram * M) i j) := by
    intro M j t
    have := L (t • M.map (Witness.prH p)) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    simp only [hpr] at this ⊢
    rw [this, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ← Matrix.map_mul]
    rfl

  have eI : J.d.eᴴ * J.W.gram * J.d.i₀ = 0 := by
    have := congrArg Matrix.conjTranspose J.d.i₀e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this
  have eE' : J.d.eᴴ * J.W.gram * J.d.e' = 1 := by
    have := congrArg Matrix.conjTranspose J.d.e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, fun r => h1 i _ rfl r,
    fun r => h2 i _ (by simp only; omega) r, ?_⟩
  intro m hm
  rcases m with a | ⟨j, hj⟩
  · rw [L F.β (Sum.inl a)]
    have hcol : ∀ r, F.β r (Sum.inl a) = (J.d.i₀.map (Witness.prH p) * F₀.β) r a := fun r => h0 r a
    rw [Matrix.mul_apply]
    simp only [hcol]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← Matrix.map_mul, eI, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
      Matrix.zero_apply]
  · by_cases hjρ : j < ρ
    · have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * p.xi ^ (ρ - j) * p.pr (J.d.e r ⟨j, hjρ⟩) :=
        fun r => h1 ⟨j, hjρ⟩ _ rfl r
      simp only [hcol]
      rw [Ls, J.d.ee, Matrix.zero_apply, map_zero, mul_zero]
    · set i' : Fin ρ := ⟨2 * ρ - 1 - j, by omega⟩ with hi'
      have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (J.d.e' r i') :=
        fun r => h2 i' _ (by simp only [hi']; omega) r
      simp only [hcol]
      have hne : i ≠ i' := by
        intro h
        apply hm
        rw [h]
        simp only [hi', Sum.inr.injEq, Fin.mk.injEq]
        omega
      rw [Ls, eE', Matrix.one_apply_ne hne, map_zero, mul_zero]

end GlobalTheory.LocMod.JacCols
end
