module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.LatCong

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem latV_mono' (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem latO_le_right (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (N' M' : Lat T) (P : Pl D → Prop)
    (h : latV T N' P ≤ latV T M' P) :
    latO S T LS (N' : Set _) P ≤ latO S T LS (M' : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let c : Fin S.rank → AE D := fun j => (1 : AF D.host.F) ⊗ₜ[D.host.F] (a * ∑ k, star (s k) * S.gram k j)
  let Φ : (Fin T.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun u => Matrix.of fun i j => u i * c j) (by
      intro u u'; ext i j; simp [add_mul])
  have key : latV T M' P ≤ (latO S T LS (M' : Set _) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, s, hs, m, hm, ?_⟩
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have hmem : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) ∈ latV T N' P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, t, ht, rfl⟩
  have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * t i)) =
      Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
    ext i j
    simp only [Φ, c, AddMonoidHom.mk'_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [e] at h2
  exact h2

theorem latO_le_left (S T : HSp D) (N M : Lat S) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop)
    (h : latV S N P ≤ latV S M P) :
    latO S T (N : Set _) LT P ≤ latO S T (M : Set _) LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  let Φ : (Fin S.rank → AE D) →+ WO S T :=
    AddMonoidHom.mk' (fun y => Matrix.of fun i j => ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i)) *
      ∑ k, cA D (y k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)) (by
      intro u u'; ext i j; simp [map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add])
  have gen : ∀ (γ : Af D.host.F) (x : Fin S.rank → D.host.E),
      Φ (fun k => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 * x k)) =
        Matrix.of fun i j => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (a * t i * ∑ k, star (x k) * S.gram k j) := by
    intro γ x
    ext i j
    simp only [Φ, AddMonoidHom.mk'_apply, Matrix.of_apply, one_mul]
    change (1 ⊗ₜ[D.host.F] (a * t i)) * ∑ k, (pairA D.host.F 0 γ ⊗ₜ[D.host.F] star (x k)) * (1 ⊗ₜ[D.host.F] S.gram k j) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Finset.mul_sum, one_mul, ← TensorProduct.tmul_sum]
  have key : latV S M P ≤ (latO S T (M : Set _) LT P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, hγP, b, hb, m, hm, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, gen]
    exact AddSubgroup.subset_closure ⟨γ, hγ, hγP, a, ha, m, hm, t, ht, rfl⟩
  have hmem : (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s k)) ∈ latV S N P :=
    AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, s, hs, rfl⟩
  have h2 := AddSubgroup.mem_comap.1 (key (h hmem))
  rw [gen] at h2
  exact h2



theorem latV_le_of_local (S : HSp D) (N M : Lat S) (hN : Submodule.IsLattice D.host.E N)
    (hM : Submodule.IsFullLattice D.host.E M) (P : Pl D → Prop)
    (h : ∀ p, P p → latV S N (· = p) ≤ latV S M (· = p)) : latV S N P ≤ latV S M P := by
  classical
  obtain ⟨d, hd, hNM⟩ := exists_int_smul_le N M hN.fg hM.span_eq_top
  obtain ⟨B, hB⟩ : ∃ B : Finset (Pl D), ∀ w : Pl D, w ∉ B → ((d : 𝓞 D.host.F)) ∉ w.asIdeal :=
    ⟨(finite_places_int (D := D) d hd).toFinset, fun w hw h' => hw ((Set.Finite.mem_toFinset _).2 h')⟩
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hb
  subst hb
  let Ψ : Af D.host.F →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun β => fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) (by
      intro β β'
      funext i
      rw [Pi.add_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero 0).symm rfl)
  have hsplit : α = ∑ v ∈ B, α * indQ D {v} + α * (1 - indQ D B) := by
    have e : indQ D B = ∑ v ∈ B, indQ D {v} := by simp only [indQ, Finset.sum_singleton]
    rw [← Finset.mul_sum, ← e, ← mul_add, add_sub_cancel, mul_one]
  show Ψ α ∈ latV S M P

  rw [hsplit, map_add (f := _), map_sum]
  refine add_mem (AddSubgroup.sum_mem _ fun v _ => ?_) ?_
  · by_cases hv : P v
    · have h1 : Ψ (α * indQ D {v}) ∈ latV S N (· = v) := by
        refine AddSubgroup.subset_closure ⟨α * indQ D {v}, fun w => ?_, fun w hw => ?_, 1, rfl, x, hx, rfl⟩
        · rw [map_mul, evalV_indQ]
          split_ifs
          · rw [mul_one]; exact hα w
          · rw [mul_zero]; exact zero_mem _
        · rw [map_mul, evalV_indQ, if_neg (by rwa [Finset.mem_singleton]), mul_zero]
      exact latV_mono' S M (fun w hw => hw ▸ hv) (h v hv h1)
    · have h0 : α * indQ D {v} = 0 := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α * indQ D {v}) = evalV D.host.F w 0
        rw [map_mul, evalV_indQ, map_zero]
        split_ifs with hw
        · rw [Finset.mem_singleton] at hw
          subst hw
          rw [hP w hv, zero_mul]
        · rw [mul_zero]
      rw [h0, map_zero]
      exact zero_mem _
  · generalize hβ : α * (1 - indQ D B) = β
    have hβB : ∀ w, evalV D.host.F w β = if w ∈ B then 0 else evalV D.host.F w α := by
      intro w
      rw [← hβ, map_mul, map_sub, map_one, evalV_indQ]
      split_ifs
      · rw [sub_self, mul_zero]
      · rw [sub_zero, mul_one]
    have hsm : ∀ w, evalV D.host.F w (((d : D.host.F))⁻¹ • β) =
        algebraMap D.host.F (w.adicCompletion D.host.F) ((d : D.host.F))⁻¹ * evalV D.host.F w β := by
      intro w
      rw [map_smul, Algebra.smul_def]
    refine AddSubgroup.subset_closure ⟨((d : D.host.F))⁻¹ • β, fun w => ?_, fun w hw => ?_,
      1, rfl, d • x, hNM x hx, ?_⟩
    · by_cases hw : w ∈ B
      · rw [hsm, hβB, if_pos hw, mul_zero]
        exact zero_mem _
      · have hwv : ((d : 𝓞 D.host.F)) ∉ w.asIdeal := hB w hw
        have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
          have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hwv
          have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
          have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
            map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
          exact h2.trans (h4 ▸ h1)
        have hαw := hα w
        have e1 : evalV D.host.F w β = evalV D.host.F w α := by rw [hβB, if_neg hw]
        rewrite [map_smul, e1]
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
        rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
        exact hαw
    · have e0 : evalV D.host.F w β = 0 := by
        rw [hβB]
        split_ifs
        · rfl
        · exact hP w hw
      rewrite [map_smul, e0]
      exact smul_zero _
    · funext i
      show pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) =
        pairA D.host.F 0 (((d : D.host.F))⁻¹ • β) ⊗ₜ[D.host.F] (1 * (d • x i))
      exact pairA_tmul_int_gen d hd β (x i)

theorem latO_congr : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M →
    IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop),
    (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) →
    latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  intro D S T N M N' M' hN hM hN' hM' P hloc
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ
  have hS : latV S N P = latV S M P := le_antisymm
    (latV_le_of_local S N M hN.1 (hfull S M hM) P fun p hp => (hloc p hp).1.le)
    (latV_le_of_local S M N hM.1 (hfull S N hN) P fun p hp => (hloc p hp).1.ge)
  have hT : latV T N' P = latV T M' P := le_antisymm
    (latV_le_of_local T N' M' hN'.1 (hfull T M' hM') P fun p hp => (hloc p hp).2.le)
    (latV_le_of_local T M' N' hM'.1 (hfull T N' hN') P fun p hp => (hloc p hp).2.ge)
  apply le_antisymm
  · exact (latO_le_right S T _ N' M' P hT.le).trans (latO_le_left S T N M _ P hS.le)
  · exact (latO_le_right S T _ M' N' P hT.ge).trans (latO_le_left S T M N _ P hS.ge)

end GlobalTheory.FinPl.LatCong

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.FullLatFrame

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : GlobalTheory.FinPl.SplitPt D k)

theorem e_int : finPart D q.e ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q]; exact (q.int_iff 1).1 (one_mem _)

theorem pr_int_mem (o : 𝓞 D.host.E) : q.pr (incA D (o : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem pr_pair_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) :
    q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨α, hα, 1, ?_⟩)
  rfl

variable {S : HSp D}

def aux₃ (x : Fin S.rank → D.host.E) : Fin S.rank → k := fun a => q.pr (incA D (x a))

theorem splitPointComponent_mem_span_of_lattice_generators {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    aux₃ q x ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  rw [← hG] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have h : aux₃ q (0 : Fin S.rank → D.host.E) = 0 := by funext a; simp [aux₃]
    rw [h]; exact zero_mem _
  | add x y _ _ hx hy =>
    have h : aux₃ q (x + y) = aux₃ q x + aux₃ q y := by funext a; simp [aux₃]
    rw [h]; exact add_mem hx hy
  | smul o x _ hx =>
    have h : aux₃ q (o • x) = (⟨_, pr_int_mem q o⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show q.pr (incA D (o • x a)) = q.pr (incA D (o : D.host.E)) * q.pr (incA D (x a))
      rw [Algebra.smul_def, map_mul, map_mul]
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem pr_mem_span {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L (· = q.v)) :
    (fun a => q.pr (y a)) ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have h : (fun a => q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x a))) =
        (⟨_, pr_pair_mem q hα⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show _ = q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * q.pr (incA D (x a))
      rw [← map_mul]
      congr 1
      change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x a)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]; exact Submodule.smul_mem _ _ (splitPointComponent_mem_span_of_lattice_generators q G hG hx)
  | zero =>
    have h : (fun a => q.pr ((0 : Fin S.rank → AE D) a)) = 0 := by funext a; simp
    rw [h]; exact zero_mem _
  | add y z _ _ hy hz =>
    have h : (fun a => q.pr ((y + z) a)) = (fun a => q.pr (y a)) + fun a => q.pr (z a) := by funext a; simp
    rw [h]; exact add_mem hy hz
  | neg y _ hy =>
    have h : (fun a => q.pr ((-y) a)) = -fun a => q.pr (y a) := by funext a; simp
    rw [h]; exact neg_mem hy

def latW (L : GlobalTheory.FinPl.Lat S) : Submodule 𝒪[k] (Fin S.rank → k) where
  carrier := {w | (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)}
  add_mem' := by
    intro x y hx hy
    have h : (fun i => q.sec ((x + y) i)) = (fun i => q.sec (x i)) + fun i => q.sec (y i) := by funext i; simp
    simp only [Set.mem_setOf_eq] at *
    rw [h]; exact add_mem hx hy
  zero_mem' := by
    have h : (fun i => q.sec ((0 : Fin S.rank → k) i)) = 0 := by funext i; simp
    simp only [Set.mem_setOf_eq]
    rw [h]; exact zero_mem _
  smul_mem' := by
    intro c x hx
    have h : (fun i => q.sec ((c • x) i)) = fun i => q.sec (c : k) * q.sec (x i) := by
      funext i; rw [← GlobalTheory.FinPl.FrameLat.sec_mul q]; rfl
    simp only [Set.mem_setOf_eq] at *
    rw [h]
    exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV ((q.int_iff c).1 c.2) hx

theorem mem_latW {L : GlobalTheory.FinPl.Lat S} (w : Fin S.rank → k) :
    w ∈ latW q L ↔ (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := Iff.rfl

end GlobalTheory.LocMod.FullLatFrame

namespace GlobalTheory.LocMod.FullLatFrame

end GlobalTheory.LocMod.FullLatFrame
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
  GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinearHalf

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (NumberField.RingOfIntegers D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E)}
  {a : AE D} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D}

section Model

variable (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (ha : a * a = a)
  (hinf : infPart D a = 0) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
  (he : IsSplitIdem D e) (hae : a * e = e)
  (hfix : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀)

include hW hS hT ha hinf hc hf hTm he hae hfix

theorem base_enlarge {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    om (g, h) f₀ = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).relIndex
      ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) •
      Tm fun t => halfInd a (latO S T ΛS ΛT fun _ => True) (actO S T g⁻¹ h⁻¹ t) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  haveI := finite_enlarge inferInstance inferInstance he.1 hle
  obtain ⟨R, r1, r2, r3⟩ := exists_reps ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e)
    ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)
  have hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u := fun u hu =>
    ⟨(r2 u hu).1, (isHalf_iff S T).2 (r2 u hu).2⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True) := fun w hw hwe =>
    (existsUnique_congr fun v => and_congr_right fun hv =>
      ⟨fun h => h.1, fun h => ⟨h, (isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hwe (hR v hv).2)⟩⟩).1
      (r3 w ⟨hw, (isHalf_iff S T).1 hwe⟩)
  rw [om_eq_sum_lattice hW hS hT he hf hfix hg hh hx hy hR hRu hle, r1,
    model_sum hTm fun u hu => isHalf_mono hae (hR u hu).2,
    sum_halfInd he.1 hc hae (GlobalTheory.SplitScalar.idem_smul_mem he.1) (GlobalTheory.SplitLinear.suppAt_inv hg) (GlobalTheory.SplitLinear.suppAt_inv hh) hR hRu hle]

theorem law_enlarge' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  have h1 := base_enlarge hW hS hT ha hinf hc hf hTm he hae hfix hg hh
    (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  rw [← Complex.ofReal_inv, sqrt_index inferInstance inferInstance he (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle] at h1
  exact om_model_of_base D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm g h _ h1

theorem law_place' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO (ΛS := ΛS) (ΛT := ΛT) inferInstance inferInstance g⁻¹ h⁻¹
  obtain ⟨z, z1, z2⟩ := exists_scalar he T hN
  have z4 : SuppAt e T z⁻¹ := GlobalTheory.SplitLinear.suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv z1)
  have l1 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix hg (GlobalTheory.SplitLinear.suppAt_mul hh z4) fun w hw hwe => by
    rw [actO_scalar' z2 g h hwe]
    exact h1 w hw
  have l2 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix (suppAt_one e S) z4 fun w hw hwe => by
    rw [inv_one, inv_inv, actO_scalar z2 hwe]
    exact nsmul_mem hw N
  have l3 := l1.mul inferInstance inferInstance (l2.inv inferInstance inferInstance (fac_ne_zero _ _))
  have e1 : fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T (h * z⁻¹)) =
      fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h) * fac S T χS χT (detAt e he.1 S 1) (detAt e he.1 T z⁻¹) := by
    rw [← fac_mul, ← MonoidHom.map_mul, ← MonoidHom.map_mul, mul_one]
  exact l3.congr (by rw [inv_one, mul_one]) (mul_inv_cancel_right _ _)
    (by rw [e1, mul_inv_cancel_right₀ (fac_ne_zero _ _)])

end Model

theorem detAt_eq {V : HSp D} (he : e * e = e) {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    x = detAt e he V g :=
  Units.ext (hx.trans (isDetAt_detAt e he V g).symm)

theorem law_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT e f₀ Tm hW hS hT he hf hfix hTm g h hg hh x y hx hy Φ hΦ
  have hinf : infPart D e = 0 := GlobalTheory.PlaceModelSum.IsOrthSum.infPart_eq
    ⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩
  rw [detAt_eq he.1 hx, detAt_eq he.1 hy]
  exact law_place' hW hS hT he.1 hinf he.2.1 hf hTm he he.1 hfix hg hh Φ hΦ

end GlobalTheory.SplitLinearHalf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceLocalCharacter_isUnramified_of_heckeUnramified : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (GlobalTheory.SplitLinAt.lam p χ r) := by
  first | exact @GlobalTheory.SplitLinUnram.lam_unram | exact GlobalTheory.SplitLinUnram.lam_unram | (intros; apply GlobalTheory.SplitLinUnram.lam_unram <;> assumption)
end
