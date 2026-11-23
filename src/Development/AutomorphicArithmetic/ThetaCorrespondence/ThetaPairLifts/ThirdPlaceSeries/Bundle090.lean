module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafIPOfTwoConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
public import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle368
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.IPbProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.BigTop.Fun.IPbProof
namespace GlobalTheory.BigTop.Fun
open GlobalTheory.BigTop.Fun.IPbProof
theorem ipb_of_lamLow_alt : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound := by
  intro hL
  refine ⟨0, ?_⟩
  intro CF hCF
  refine hL.imp ?_
  intro eps Fm CH heps h hdiv
  refine ⟨max 0 (max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3))), fun C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 9, fun x hx hle i p hp d _ => ?_⟩
  have h6 := hx0 x hx (le_of_max_le_left hle) i p hp C
  have hC0 : 0 ≤ C := (le_max_left _ _).trans hC
  have hC1 : max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3)) ≤ C := (le_max_right _ _).trans hC
  have hb : 1 ≤ p.Z.b := one_le_b (Fm.L x i)
  have hlb : Real.log p.Z.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by rw [← hlb]; exact Real.log_nonneg hb
  set P5 := Fm.params x hx i
  have hS := Fm.sizes x hx i
  have hx9 : 9 ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact le_of_max_le_right hle
  have hLp := Formalism.L2.DIV.Arith4S.Lp_le_La (Fm.L x i) p.Del p.h0 P5 hS hx9
  rw [Formalism.L2.DIV.ofRecord_La, Fm.params_CYL x hx i, Fm.Ct_eq x i] at hLp
  have hLa := La_le_three (Fm.L x i) hS
  have hY : 0 < Fm.CYL := (Fm.params_CYL x hx i) ▸ P5.CYL_pos
  set c : ℝ := 3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3) with hc
  have hc0 : 0 ≤ c := by have := le_max_right Fm.Ct 5; rw [hc]; linarith
  set Lp := (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).Lp
  have hLp0 : 0 ≤ Lp := Formalism.L2.DIV.NumDatum.Lp_nonneg _
  have hLp3 : Lp ≤ 3 * c * (Fm.L x i).sc.L := by nlinarith
  have hNV : ((Fm.D x i).R.nV : ℝ) ≤ (d.O.N : ℝ) := by
    have hm := (Fm.D x i).R.two_le_m
    have h1 : (Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1 ≤
        (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (Fm.D x i).R.nV ≤ d.O.N := by
      show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t ≤
        (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)
      omega
    exact_mod_cast h2
  have hf0 : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnv0 : (0 : ℝ) ≤ ((Fm.D x i).R.nV : ℝ) := Nat.cast_nonneg _
  have hsq : ((Fm.D x i).R.nV : ℝ) ^ 2 ≤ (d.O.N : ℝ) ^ 2 := pow_le_pow_left₀ hnv0 hNV 2
  have hA0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp := by positivity
  have hA : ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp ≤
      ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L) := by
    gcongr
  have hB0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by positivity
  have hcs : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
      3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by
    have e1 : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    have e2 : max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L)) :=
      mul_le_mul_of_nonneg_left hA (le_max_right _ _)
    have e3 : max Fm.Csz 0 * c * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤
        C * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) :=
      mul_le_mul_of_nonneg_right hC1 hB0
    nlinarith
  refine GlobalTheory.InfinitePlacesProbe.clauseB_of_lifts (p.S false) (p.S true) (p.N C CH) d.O hC0 hb ⟨rfl, rfl, rfl⟩ h6
    (by simp; rfl) fun j => ?_
  have hm0 : 0 ≤ ∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ :=
    Finset.sum_nonneg fun ρ _ => Real.log_natCast_nonneg _
  have e : (p.N C CH).l6 j = (∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ) -
      Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) - C * 0 := rfl
  rw [e, hlb]
  show -(3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ _
  linarith
end GlobalTheory.BigTop.Fun
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop.LComm
variable {D : D7}
end GlobalTheory.MiTop.LComm
end
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.linkComm_of_laws_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f k _ _ _ _ ι o ε S₀ hU hc ht hnd _ hinj hne h0 hsur n h
  have hall : ∀ η : ι → 𝓀[k]ˣ, ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧
      ∀ φ y, (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u (S φ)).1 y =
        o.S (fun _ => η) 0 ((chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) := by
    intro η
    obtain ⟨α⟩ := hne W.P.A3.A.μ0
    have hR := (ht W.P.A3.A.μ0).2.2.2.2
    refine GlobalTheory.T.levelPrime_operators_stepZero_scale_norms D u (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ hc.inf hU (hc.x 0 (Nat.zero_le _)).cpt k ι o.p o.I o.q o.χ o.hχ (o.β 0) (o.Q 0)
      hnd hinj (fun φ y i => ?_) η (fun φ => ?_)
    · have := (hR.ram 0 (Nat.zero_le _) _ (h0 _ φ).1 α y).2 i
      rw [(h0 _ φ).2 α y] at this
      exact this
    · obtain ⟨h1, h2⟩ := hR.S₀ η _ (h0 _ φ).1
      obtain ⟨φ', e⟩ := hsur _ _ h1
      refine ⟨φ', fun y => ?_⟩
      have := h2 α y
      rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
      exact this
  choose S r hr hS hrd using hall
  have hS0 : ∀ t η φ, S₀ t η (_root_.GlobalTheory.MiTop.col0_alt f t φ) = _root_.GlobalTheory.MiTop.col0_alt f t (S η φ) := by
    intro t η φ
    obtain ⟨α⟩ := hne t
    obtain ⟨h1, h2⟩ := (ht t).2.2.2.2.S₀ η _ (h0 t φ).1
    obtain ⟨φ', e⟩ := hsur _ _ h1
    rw [e]
    congr 1
    apply (D.eMu u).injective
    apply Subtype.ext
    refine LComm.chart0_inj (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ _ _ (fun y => ?_)
    have := h2 α y
    rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
    rw [this, hrd]
  obtain ⟨A, a, ha, hA, hA'⟩ := LComm.iter_equiv S r hr hS ε n
  refine ⟨A, a, o.cS n, ha, hA, ?_, fun t φ F => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ ?_
    refine Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne'
    exact Nat.cast_pos.2 Nat.card_pos
  · obtain ⟨t1, t2, t3, t4, t5⟩ := ht t
    rw [GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero D f.c k ι o (f.t t) ε (S₀ t) t1 t2 t3 t4 t5 n h _ (h0 t φ).1 F,
      LComm.iterS_comm (fun η φ => S η φ) (S₀ t) (_root_.GlobalTheory.MiTop.col0_alt f t) (hS0 t) ε n φ, hA']
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top
variable {D : D7}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem tcol_alt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (i : ℕ) (ψ : (f.t t).Col 0) :
    (f.t t).col i ψ = Formalism.ThetaLiftIndependence.chainOpM (D.chTw u (W.P.I.tup t)).wt (D.chTw u (W.P.I.tup t)).Kmap i ψ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (f.t t).K i ((f.t t).col i ψ) = _
    rw [ih]; rfl
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
section G
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
end G
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop
open Classical
open GlobalTheory.MiTop.TailColumnRecursion Formalism.L2.Forms
theorem linkTail_of_topReadAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → (∀ t, W.P.I.tup t = D.what₂.mu0 → ∀ φ : D.what₂.Mu u, HEq (_root_.GlobalTheory.MiTop.col0_alt f t φ) (D.eMu u φ).1) → _root_.GlobalTheory.MiTop.LinkTailCondition f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hTR h0 n h t φ F F' hFF G hG
  obtain ⟨hJ, -, hall⟩ := hTR
  have hR := (hall t).2 F F' hFF
  have hex : ∃ G0, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT (W.P.I.tup t) G0 (_root_.GlobalTheory.Fam.leadingLinearMap W t F') := ⟨_, hR⟩
  have hspec := hex.choose_spec
  show _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t)
    (Eq.rec (motive := fun n _ => (D.chTw u (W.P.I.tup t)).cls n → (D.chTw u (W.P.I.tup t)).Y n → ℂ)
      ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) h) G.1 = _
  rw [hG, _root_.GlobalTheory.MiTop.TailColumnRecursion.tcol_alt, rec_chain]
  unfold _root_.GlobalTheory.Fam.tailCoefficient
  rw [dite_eq_left hex]
  by_cases hμ : W.P.I.tup t = D.what₂.mu0
  · rw [dite_eq_left hμ]
    refine referenceTuple_familyPeriod_eq_period u _ hμ _ φ (h0 t hμ φ) _ _ ?_
    have hv : ∀ z ∈ (D.fm u).ptC, ∀ c, (W.R.T.cols.forms u).valP.eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range]
      exact fic_val _ _ _ _ (((W.R.T.cols.forms u).valP.ptC z).1 hz) c
    exact reads_uniq _ _ _ _ (W.R.T.cols.forms u).jM hv (W.R.T.cols.forms u).per.2.1 (W.R.T.cols.forms u).per.2.2
      (pos_0 (W.R.T.cols.forms u)) (hspec.1 hμ) (hR.1 hμ)
  · rw [dite_eq_right hμ, D.perCol_tie u _ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
    have hv : ∀ z ∈ (ex.tw.fm u (W.P.I.tup t)).ptC, ∀ c, (W.R.T.tw.pt.val u _ hμ).eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range, ← sg_eq (W.R.T.tw.pt.val u _ hμ) (W.R.T.cols.forms u).valP]
      exact fic_val _ _ _ _ (((W.R.T.tw.pt.val u _ hμ).ptC z).1 hz) c
    rw [reads_uniq _ _ _ _ (W.R.T.tw.ptE.jM u _) hv (W.R.T.tw.ptE.per u _ hμ).2.1 (W.R.T.tw.ptE.per u _ hμ).2.2
      (pos_G (W.R.T.tw.pt.val u _ hμ)) (hspec.2 hμ) (hR.2 hμ)]
    rfl
end GlobalTheory.MiTop
end
end
end

section



section
noncomputable section
open Filter Asymptotics
namespace GlobalTheory.BigTop.Fun
theorem existsIntegralMultiple_holds_alt : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := exists_log_le_two_rpow he
  refine ⟨x0, fun x hx hle i p _ => ?_⟩
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hx
  have hZx : p.Z.x = x := hsx
  have hZb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  show 1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
  rw [hZx, hZb, Real.log_exp]
  have h1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1.le he.le
  exact ⟨hx1.le, h1, by linarith [hx0 x hle]⟩
end GlobalTheory.BigTop.Fun
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.RamSum
section Norms
variable {F : Type} [Field F] [NumberField F]
end Norms
end GlobalTheory.BigTop.Fun.RamSum
namespace GlobalTheory.BigTop.Fun
open RamSum
theorem ramified_sums_seventh_bound_alt : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound' := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ _ => ?_⟩⟩⟩
  refine ⟨42, fun C hC => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ d _ => ?_⟩
  obtain ⟨-, -, hg, h1, h2, -⟩ := hF.1.2.2.2.2.2.2.2.2 x hx i
  have h3 := hF.2.2.1 x hx i
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine leaves_of_sum d.O C p.Z.b (Real.log_nonneg hb) (d.G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) (fun v _ => isPrimePow_absNorm v)
    (ramifiedPlaces_sum_log_absNorm_le d.G.pl (Fm.L x i).sc hg h1 h2 h3) (fun v _ => ?_)
    (le_PPF d.O hC hb ?_ ?_ ((Fm.D x i).host.g_prime 0).pos ((Fm.D x i).host.g_prime 1).pos (Fm.D x i).host.pde_prime.pos
      (Fm.D x i).host.pde'_prime.pos (discr_ne_zero _))
  · unfold FunIn.O FunIn.data
    dsimp only
    split_ifs <;> omega
  · have := (Fm.D x i).R.m_le_f
    have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.f
    unfold Ranks.f Ranks.n
    omega
  · have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.k + (Fm.D x i).R.m
    omega
end GlobalTheory.BigTop.Fun
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem desHLeaf_alt : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨0, fun C _ => ?_⟩
  have hW : PageWin Fm := hF.2.1
  refine ⟨max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps)), fun x hx hx0 i p _ d _ => ?_⟩
  have hx1 : 1 < x := lt_trans Fm.one_lt_family_threshold hx
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx0) heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, -⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  refine ⟨⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩, ?_⟩
  show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
  exact (lcLeOfCloud d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
    (fun τ j => cloudIcc (Fm.L x i) τ j)).trans (scLeB (Fm.params x hx i))
end GlobalTheory.BigTop.Fun.Close
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun.PolBound
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun.PolBound
open Formalism.BasicNotions Formalism.MainNotions NumberField
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun
open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound
theorem desPol_alt : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith
end GlobalTheory.BigTop.Fun
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem bundle_of_rows_alt : _root_.GlobalTheory.BigTop.Fun.BundleCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  exact ⟨hR.wf false, Formalism.IndefR.Links.primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim,
    Formalism.IndefR.Links.primRows3_data hp.ok hp.sep p.charW hp.prim⟩
end GlobalTheory.BigTop.Fun
end
end
end
