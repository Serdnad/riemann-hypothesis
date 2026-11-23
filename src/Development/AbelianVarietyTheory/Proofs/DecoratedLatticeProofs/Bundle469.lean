module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle463
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle370
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.PlaceSupp

theorem supp_ctr : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F₁ hF₁ F₂ hF₂ x hx hne
  have hs := Gi.hs
  obtain ⟨μ, hμ, hμu, -, h2⟩ := hch
  obtain ⟨hPhi, hLev⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq Gi.k _ _ Gi.S (Fin D.R.t) μ hμ hμu
  have a₀ : j + (2 * σ + 1 + 1 + 1) = Gi.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = Gi.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = Gi.s + 1 := by omega
  have b₀ : j + (2 * σ + 1 + 1) = Gi.s := by omega
  have b₁ : j + 1 + (2 * σ + 1) = Gi.s := by omega
  obtain ⟨T₁, hT₁, hO₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1)) (Gi.FY j _ a₀) (Gi.FY (j + 1) _ a₁)
    c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (Gi.latY j _ a₀) (Gi.latY (j + 1) _ a₁)).2 F₁ hF₁
  obtain ⟨T₂, hT₂, hO₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V (j + 1)) (c.V (j + 1 + 1)) (Gi.FY (j + 1) _ a₁)
    (Gi.FY (j + 1 + 1) _ a₂) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N (j + 1)) (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega))
    (hv.sd (j + 1 + 1) (by omega)) (Gi.latY (j + 1) _ a₁) (Gi.latY (j + 1 + 1) _ a₂)).2 F₂ hF₂
  obtain ⟨O₁, h1⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, h1'⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have m₁ : (Gi.S.T (Fin D.R.t)).Phi j _ b₀ ∈ GlobalTheory.SplitWeil.SB _ := (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ b₀
  have m₂ : (Gi.S.T (Fin D.R.t)).Phi (j + 1) _ b₁ ∈ GlobalTheory.SplitWeil.SB _ :=
    (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 (j + 1) _ b₁
  have e₁ := (Gi.eg_is j _ b₀).2 T₁ hT₁ O₁ ⟨_, m₁⟩ h1 rfl
  have e₂ := (Gi.eg_is (j + 1) _ b₁).2 T₂ hT₂ O₂ ⟨_, m₂⟩ h1' rfl
  rw [hO₁ O₁ h1] at e₁
  rw [hO₂ O₂ h1'] at e₂
  rw [← e₁, ← e₂, ← (ht.sFB j σ h).1] at hne
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by
        have h3 := Gi.sc_unit j
        rw [h0, map_zero] at h3
        exact zero_ne_one h3
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j _ a₀
      G₁ := Gi.FY (j + 1) _ a₁
      G₂ := Gi.FY (j + 1 + 1) _ a₂
      bes := Gi.bes j (σ + 1) h _ a₀
      jac := Gi.jac j (σ + 1) h _ a₁
      bes' := by
        rw [← Gi.sc_step j]
        exact Gi.bes (j + 1 + 1) σ (idx_step h) _ a₂ }
  obtain ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμ) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ F (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (h2 j σ h).1
    T₁ T₂ hT₁ hT₂ ⟨_, m₁⟩ ⟨_, m₂⟩ (hPhi j _ b₀).symm (hPhi (j + 1) _ b₁).symm x hx hne
  rw [(hLev (j + 1 + 1) _ a₂).1] at huk
  exact ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩

end GlobalTheory.SeeSaw.PlaceSupp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPlaceSplit

variable {D : D7}

theorem coeff_mul_eq {G : Type} [AddMonoid G] (x y : AddMonoidAlgebra ℂ G) :
    (x * y).coeff = x.coeff.sum fun g a => y.coeff.sum fun h b => Finsupp.single (g + h) (a * b) := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]

theorem aconv_eq_prod {G : Type} [AddCommMonoid G] (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv l) = (l.map AddMonoidAlgebra.ofCoeff).prod := by
  induction l with
  | nil =>
    apply AddMonoidAlgebra.ext
    rw [List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_ofCoeff]
    rfl
  | cons e l ih =>
    apply AddMonoidAlgebra.ext
    rw [List.map_cons, List.prod_cons, ← ih, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff,
      AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff]
    rfl

theorem support_prod_mem {G ι : Type} [AddCommMonoid G] (M : AddSubmonoid G) (s : Finset ι) (g : ι → G →₀ ℂ)
    (h : ∀ i ∈ s, ∀ y ∈ (g i).support, y ∈ M) :
    ∀ y ∈ (∏ i ∈ s, AddMonoidAlgebra.ofCoeff (g i)).coeff.support, y ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hy
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
    exact M.zero_mem
  | insert a s ha ih =>
    intro y hy
    rw [Finset.prod_insert ha, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff] at hy
    obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
    obtain ⟨z, hz, hy3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy2)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy3)]
    exact M.add_mem (h a (Finset.mem_insert_self a s) x hx)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) z hz)

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO hO
  simp

theorem comb_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AddMonoidAlgebra ℂ (WO S T))
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (a * b).coeff f = comb ψ S T a.coeff (comb ψ S T b.coeff f) := by
  have hz : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have ha : ∀ u (r r' : ℂ), (r + r') • heisO ψ S T u f = r • heisO ψ S T u f + r' • heisO ψ S T u f :=
    fun u r r' => add_smul _ _ _
  rw [GlobalTheory.HeisComb.comb_comb, coeff_mul_eq, GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha]
  simp only [Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha, Finsupp.sum_single_index, zero_smul]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, symplOH, h x hx y hy, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (b : WO S T →₀ ℂ)
    (h : ∀ y ∈ b.support, symplO S T u y = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (comb ψ S T b f) = comb ψ S T b (heisO ψ S T u f) := by
  unfold comb
  rw [GlobalTheory.HeisComb.heisO_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T u y = 0 := by unfold symplOH; rw [h y hy, mul_zero]
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm y u, h0, GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]

theorem map_infPart_of_mxAt {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {y : Mx D m n} (hy : GlobalTheory.FinPl.MxAt P y) :
    y.map (infPart D) = 0 := by
  funext a b
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact (RingHom.mem_ker).1 (Submodule.mem_inf.1 (hy a b)).1

end GlobalTheory.TwistPlaceSplit

namespace GlobalTheory.TwistPlaceSplit



theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  intro D c v t w F hc hv hP j hj i Ψ₁ hΨ
  classical
  set v₀ := (F.Q i).q.v with hv₀def
  have hv₀ : v₀ ∈ w.Q := (hP.places v₀).2 ⟨i, rfl⟩

  have hat : ∀ i', ∀ u ∈ ((F.Q i').eL j).support, GlobalTheory.FinPl.MxAt (· = (F.Q i').q.v) u := by
    intro i' u hu
    have hs := (F.Q i').hs
    obtain ⟨d, hd⟩ : ∃ d, j + d = (F.Q i').s := ⟨(F.Q i').s - j, by omega⟩
    exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (F.Q i').q u (((F.Q i').eL_at j d hd).1 u hu)

  let M : AddSubmonoid (WO (c.V j) (c.V (j + 1))) :=
    { carrier := {y | (∀ x, GlobalTheory.FinPl.MxAt (· = v₀) x → symplO _ _ x y = 0) ∧ y.map (infPart D) = 0}
      add_mem' := fun {y y'} hy hy' => ⟨fun x hx => by rw [symplO_add_right, hy.1 x hx, hy'.1 x hx, add_zero], by
        rw [Matrix.map_add _ (map_add (infPart D)), hy.2, hy'.2, add_zero]⟩
      zero_mem' := ⟨fun x _ => symplO_zero_right _ _ x, by
        funext a b
        simp⟩ }
  have hM : ∀ i' ∈ Finset.univ.erase i, ∀ y ∈ ((F.Q i').eL j).support, y ∈ M := by
    intro i' hi' y hy
    have hne : v₀ ≠ (F.Q i').q.v := fun e => Finset.ne_of_mem_erase hi' (hP.inj e).symm
    exact ⟨fun x hx => GlobalTheory.FinPl.OverSwap.symplO_eq_zero_of_ne hne hx (hat i' y hy), map_infPart_of_mxAt (hat i' y hy)⟩
  set B := ∏ i' ∈ Finset.univ.erase i, AddMonoidAlgebra.ofCoeff ((F.Q i').eL j) with hB
  have hb : ∀ y ∈ B.coeff.support, y ∈ M := support_prod_mem M _ (fun i' => (F.Q i').eL j) hM
  have hprod : w.eQ j = (AddMonoidAlgebra.ofCoeff ((F.Q i).eL j) * B).coeff := by
    rw [hB, Finset.mul_prod_erase Finset.univ (fun i' => AddMonoidAlgebra.ofCoeff ((F.Q i').eL j)) (Finset.mem_univ i),
      ← Fin.prod_ofFn, hP.eQ j hj, ← AddMonoidAlgebra.coeff_ofCoeff (aconv _), aconv_eq_prod, List.map_ofFn]
    rfl

  have hmono : ∀ u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· = v₀),
      u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· ∈ w.Q) := by
    intro u hu
    refine AddSubgroup.closure_mono ?_ hu
    rintro x ⟨α, hα, hvα, rest⟩
    exact ⟨α, hα, fun v' hv' => hvα v' fun e => hv' (by rw [e]; exact hv₀), rest⟩
  refine ⟨comb c.ψ _ _ B.coeff Ψ₁, ⟨(GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 B.coeff Ψ₁ hΨ.1 (fun u hu => (hb u hu).2) hc.std,
    fun u hu => ?_, fun e he u hu hue => ?_⟩, ?_⟩
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt (AddSubgroup.nsmul_mem _ hu 2))),
      hΨ.2.1 u (hmono u hu)]
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)), hΨ.2.2 e he u (hmono u hu) hue]
  · rw [hprod, comb_mul _ _ _ _ _ (fun x hx y hy => (hb y hy).1 x (hat i x (by rwa [AddMonoidAlgebra.coeff_ofCoeff] at hx))),
      AddMonoidAlgebra.coeff_ofCoeff]

end GlobalTheory.TwistPlaceSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  first | exact @GlobalTheory.Core.Mi.LatLine.line_trace | exact GlobalTheory.Core.Mi.LatLine.line_trace | (intros; apply GlobalTheory.Core.Mi.LatLine.line_trace <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_symmetric_data_at_type_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  first | exact @GlobalTheory.SymReadEx.exists_symRead | exact GlobalTheory.SymReadEx.exists_symRead | (intros; apply GlobalTheory.SymReadEx.exists_symRead <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.form_translate_real_point_read_by_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  first | exact @GlobalTheory.AdForm.TopTranslate.top_translate | exact GlobalTheory.AdForm.TopTranslate.top_translate | (intros; apply GlobalTheory.AdForm.TopTranslate.top_translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liveCharts_kernel_eq_classSum_jets : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  first | exact @GlobalTheory.AdForm.ClsKLive.kval | exact GlobalTheory.AdForm.ClsKLive.kval | (intros; apply GlobalTheory.AdForm.ClsKLive.kval <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastPeriod_law_movedLevel : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  first | exact @GlobalTheory.AdForm.TopInv.law_top | exact GlobalTheory.AdForm.TopInv.law_top | (intros; apply GlobalTheory.AdForm.TopInv.law_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.last_space_moved_level_class_points_representatives : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  first | exact @GlobalTheory.ClassPtReps.isReps_stabOrd_top | exact GlobalTheory.ClassPtReps.isReps_stabOrd_top | (intros; apply GlobalTheory.ClassPtReps.isReps_stabOrd_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QGeoAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def glOf (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) :
    GL Y k →* GA D S where
  toFun gk := Classical.choose (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 gk)
  map_one' := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    set g0 := Classical.choose (h.1 1)
    have h0 : p.IsLoc F g0 1 := (Classical.choose_spec (h.1 1)).1
    have h00 : p.IsLoc F (g0 * g0) 1 := by simpa using h.2.2 _ _ _ _ h0 h0
    have e := (Classical.choose_spec (h.1 1)).2 _ h00
    exact mul_left_cancel (a := g0) (by rw [mul_one]; exact e)
  map_mul' a b := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    have ha := (Classical.choose_spec (h.1 a)).1
    have hb := (Classical.choose_spec (h.1 b)).1
    exact ((Classical.choose_spec (h.1 (a * b))).2 _ (h.2.2 _ _ _ _ ha hb)).symm

theorem glOf_loc (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (g : GL Y k) :
    p.IsLoc F (glOf p S F g) g :=
  (Classical.choose_spec (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 g)).1

end GlobalTheory.QGeoAt


open GlobalTheory.QGeoAt in
theorem GlobalTheory.QGeoAt.geo_of_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b v hv hτ hNT PP hPP l hY hFX hFT
  obtain ⟨⟨ψk, hchar, hcond⟩, ⟨ν, hν⟩, hϖ⟩ := GlobalTheory.T.local_character_conductor_one_exists W u hW a PP (Or.inr hPP) l
  obtain ⟨ϖ, hunif, hcompl⟩ := hϖ hPP
  refine ⟨{
    k := l.k
    ν := ν
    unitVol := hν
    q := l.q
    idem := l.idem
    unit := l.unit
    ψk := ψk
    char := hchar
    cond := hcond
    ϖ := ϖ
    unif := hunif
    compl := hcompl
    s := l.s
    hs := l.hs
    FX := l.FX
    FT := l.FT
    FM := l.FM
    FY := hY.FY
    sc := hY.sc
    sc_ne := fun j h => by simpa [h] using hY.sc_unit j
    sc_step := hY.sc_step
    bes := hY.bes
    jac := hY.jac
    z₀ := fun r => (ofSplit l.q).pr (a.ζ₀ r)
    last := l.last
    tau := fun h => by rw [hτ]; exact hY.tau h
    latX := l.latX
    latM := l.latM
    latY := hY.latY
    latT := by rw [hNT]; exact l.latT
    gl := fun j d hd => glOf (ofSplit l.q) _ (hY.FY j d hd)
    gl_loc := fun j d hd g => glOf_loc (ofSplit l.q) _ (hY.FY j d hd) g
    frame := fun j d hd => by
      obtain ⟨e, he, hm⟩ := hY.frame j d hd
      refine ⟨e, he, ?_⟩
      simpa using hm
    frameTop := l.frameTop }, hFX, hFT, rfl⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

theorem step_index_le_s (J : QJ a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  change j + 2 ≤ (I.rec7 l Z).R.m at hj
  omega

def phi (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := step_index_le_s J i hj; omega))

def H (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := step_index_le_s J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (α i)))

def twAt (J : QJ a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v

def relax (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (twAt J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (phi J j hj)

def Up (a : GeoAll W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

end GlobalTheory.LevProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.weilDatum_localModel_formula : ∀ (D : D7), OmLoc D := by
  first | exact @GlobalTheory.LocOm.omLoc | exact GlobalTheory.LocOm.omLoc | (intros; apply GlobalTheory.LocOm.omLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.self_dual_lattices_top_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  first | exact @GlobalTheory.TopMove.fock_vac_moved_top | exact GlobalTheory.TopMove.fock_vac_moved_top | (intros; apply GlobalTheory.TopMove.fock_vac_moved_top <;> assumption)
end
