module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Section

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def lpS (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  Λ ⊓ (perpS (VS D) F0.X).restrictScalars (𝓞 D.host.E)

variable {D F0}

theorem sE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (ρ : lpS D F0 Λ →ₗ[𝓞 D.host.E] lpS D F0 Λ)
    (hρid : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ F0.X → ρ y = y)
    {s : Type} [Fintype s] (c : Basis s D.host.E (WbQ D F0)) (a : s → perpS (VS D) F0.X)
    (hac : ∀ i, (Submodule.Quotient.mk (a i) : WbQ D F0) = c i)
    (y : s → lpS D F0 Λ) (hya : ∀ i, (y i : (VS D).V) = a i)
    (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X)
    (hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V))
    (b : perpS (VS D) F0.X) (yb : lpS D F0 Λ) (hyb : (yb : (VS D).V) = b)
    (d : 𝓞 D.host.E) (hd0 : d ≠ 0) (o : s → 𝓞 D.host.E)
    (ho : ∑ i, o i • c i = d • (Submodule.Quotient.mk b : WbQ D F0)) :
    (sE (Submodule.Quotient.mk b) : (VS D).V) = (b : (VS D).V) - (ρ yb : (VS D).V) := by
  have hsm : ∀ (r : 𝓞 D.host.E) (v : (VS D).V),
      r • v = (algebraMap (𝓞 D.host.E) D.host.E r) • v := fun r v => (algebraMap_smul D.host.E r v).symm
  have hq : (Submodule.Quotient.mk (∑ i, o i • a i - d • b) : WbQ D F0) = 0 := by

    rw [← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply, hac, ho, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
  rw [Submodule.mem_comap] at hmem
  have hzX : ((∑ i, o i • y i - d • yb : lpS D F0 Λ) : (VS D).V) ∈ F0.X := by
    convert hmem using 1
    simp [hya, hyb]
  have hρz := hρid _ hzX
  have e := congrArg (fun u : lpS D F0 Λ => (u : (VS D).V)) hρz

  simp only [map_sub, map_sum, map_smul, Submodule.coe_sub, Submodule.coe_sum,
  Submodule.coe_smul] at e
  have h1 : ∑ i, o i • (y i : (VS D).V) - ∑ i, o i • (ρ (y i) : (VS D).V) =
      d • (yb : (VS D).V) - d • (ρ yb : (VS D).V) := by
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact e.symm
  have h2 := congrArg (fun q => ((sE q : perpS (VS D) F0.X) : (VS D).V)) ho

  simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
  hsEc] at h2
  have hd : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 := by
    intro h0
    apply hd0
    exact (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)
  apply smul_right_injective (VS D).V hd
  simp only
  rw [← hsm, ← hsm, ← h2]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [h1, hyb]

theorem exists_sE (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsFullLattice D.host.E Λ) :
    ∃ sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X,
      (∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a) ∧
      ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ := by
  classical
  have hlpfg : (lpS D F0 Λ).FG := Submodule.FG.of_le hL.fg inf_le_left
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract (lpS D F0 Λ) hlpfg F0.X
  have hlpP : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ perpS (VS D) F0.X := fun y => (Submodule.mem_inf.1 y.2).2
  have hlpΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ Λ := fun y => (Submodule.mem_inf.1 y.2).1
  have hPmem : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ perpS (VS D) F0.X :=
    fun y => Submodule.sub_mem _ (hlpP y) (hlpP (ρ y))
  have hPΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ Λ :=
    fun y => Submodule.sub_mem _ (hlpΛ y) (hlpΛ (ρ y))
  have hMlat := Mof_isLattice D F0 Λ hL.toIsLattice
  obtain ⟨s, _, c, hcv, hsM⟩ :=
    Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 D.host.E) (Mof D F0 Λ)
      (Mof_span D F0 Λ hL.span_eq_top)
  have hci : ∀ i, c i ∈ Mof D F0 Λ := fun i => by rw [hcv]; exact hsM i.2
  choose a haΛ hac using fun i => (mem_Mof D F0 Λ (c i)).1 (hci i)
  let y : s → lpS D F0 Λ := fun i => ⟨(a i : (VS D).V), Submodule.mem_inf.2 ⟨haΛ i, (a i).2⟩⟩
  let sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X :=
    c.constr D.host.E (fun i => ⟨(y i : (VS D).V) - (ρ (y i) : (VS D).V), hPmem (y i)⟩)
  have hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V) := by
    intro i
    simp only [sE, Basis.constr_basis]
  have hsE : ∀ b, (Submodule.Quotient.mk (sE b) : WbQ D F0) = b := by
    have hlin : (F0.X.comap (perpS (VS D) F0.X).subtype).mkQ ∘ₗ sE = LinearMap.id := by
      refine c.ext fun i => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.id_coe, id_eq]
      conv_rhs => rw [← hac i]
      rw [mk_eq_mk, hsEc]
      have : (y i : (VS D).V) = (a i : (VS D).V) := rfl
      rw [this, sub_sub_cancel_left]
      exact F0.X.neg_mem (hρX (y i))
    intro b
    exact LinearMap.congr_fun hlin b
  refine ⟨sE, hsE, ?_⟩
  intro m hm
  obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
  let yb : lpS D F0 Λ := ⟨(b : (VS D).V), Submodule.mem_inf.2 ⟨hbΛ, b.2⟩⟩
  obtain ⟨d, hd0, hdM⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom c (Mof D F0 Λ) hMlat.fg
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 (hdM _ hm)
  rw [sE_eq Λ ρ hρid c a hac y (fun i => rfl) sE hsEc b yb rfl d hd0 o ho]
  exact hPΛ yb

end Section

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Form

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_swap (x y : WbQ D F0) : hWb D F0 y x = star (hWb D F0 x y) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hWb_mk, hWb_mk]
  exact PI.ScalarPairDr.W.hT_swap _ _ _

theorem hWb_sepR (y : WbQ D F0) (hy : ∀ x, hWb D F0 x y = 0) : y = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show (b : (VS D).V) ∈ F0.X
  have h2 : (b : (VS D).V) ∈ orth (VS D) (orth (VS D) F0.X) := by
    rw [PI.ScalarPairDr.W.mem_orth]
    intro x hx
    rw [← perpS_eq_orth] at hx
    have h3 := hy (Submodule.Quotient.mk ⟨x, hx⟩)
    rwa [hWb_mk] at h3
  rw [PI.ScalarPairDr.W.orth_orth] at h2
  exact h2

theorem hWb_eq_of (x y : WbQ D F0) (h : ∀ a, hWb D F0 a x = hWb D F0 a y) : x = y := by
  refine sub_eq_zero.1 (hWb_sepR D F0 (x - y) (fun a => ?_))
  rw [map_sub, h a, sub_self]

theorem exists_u (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) :
    ∃ u : (VS D).V →ₗ[D.host.E] WbQ D F0,
      ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v := by
  classical
  let b := Module.finBasis D.host.E (WbQ D F0)
  let M : WbQ D F0 →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => hWb D F0 (b i))
  have hMinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, hWb D F0 (b i) y = 0 := fun i => congrFun hy i
    apply hWb_sepR D F0 y
    intro a
    rw [← b.sum_repr a]

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy',
    smul_zero, Finset.sum_const_zero]
  have hMsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hMinj
  obtain ⟨Me, hMe⟩ : ∃ Me : WbQ D F0 ≃ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E),
      ∀ x, Me x = M x := ⟨LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩, fun x => rfl⟩
  let g : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E (WbQ D F0)) → D.host.E) :=
    LinearMap.pi (fun i => (VS D).hT (sE (b i) : (VS D).V))
  refine ⟨Me.symm.toLinearMap ∘ₗ g, fun a v => ?_⟩
  have key : ∀ i, hWb D F0 (b i) (Me.symm (g v)) = (VS D).hT (sE (b i) : (VS D).V) v := by
    intro i
    have h := hMe (Me.symm (g v))
    rw [Me.apply_symm_apply] at h
    exact (congrFun h i).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← b.sum_repr a]

  simp only [map_sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.map_smulₛₗ,
  LinearMap.smul_apply, map_smul, Submodule.coe_smul, key]

end Form

section Gamma

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def gF (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X) (u : (VS D).V →ₗ[D.host.E] WbQ D F0)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + (perpS (VS D) F0.X).subtype ∘ₗ sE ∘ₗ
    ((σ : WbQ D F0 →ₗ[D.host.E] WbQ D F0) - LinearMap.id) ∘ₗ u

variable {D F0}
variable {sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X} {u : (VS D).V →ₗ[D.host.E] WbQ D F0}

theorem gF_apply (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (v : (VS D).V) :
    gF D F0 sE u σ v = v + (sE (σ (u v) - u v) : (VS D).V) := by
  rfl

theorem u_perp (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (y : perpS (VS D) F0.X) :
    u y = Submodule.Quotient.mk y := by
  apply hWb_eq_of D F0
  intro a
  rw [hu]
  conv_rhs => rw [← hsE a]
  rw [hWb_mk]

theorem u_sE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (b : WbQ D F0) :
    u (sE b : (VS D).V) = b := by
  rw [u_perp hsE hu (sE b), hsE b]

theorem u_X (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) {x : (VS D).V} (hx : x ∈ F0.X) :
    u x = 0 := by
  apply hWb_sepR D F0
  intro a
  rw [hu]
  exact hT_perp_X D F0 (sE a).2 hx

theorem u_gF (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : u (gF D F0 sE u σ v) = σ (u v) := by
  rw [gF_apply, map_add (f := _), u_sE hsE hu]
  abel

theorem gF_symm (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : gF D F0 sE u σ.symm (gF D F0 sE u σ v) = v := by
  rw [gF_apply σ.symm (gF D F0 sE u σ v), u_gF hsE hu σ v, LinearEquiv.symm_apply_apply, gF_apply σ v,
    show u v - σ (u v) = -(σ (u v) - u v) by abel, map_neg, Submodule.coe_neg, add_neg_cancel_right]

def gE (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (gF D F0 sE u σ) (gF D F0 sE u σ.symm)
    (by
      ext v
      have := gF_symm hsE hu σ.symm v
      rwa [LinearEquiv.symm_symm] at this)
    (by
      ext v
      exact gF_symm hsE hu σ v)

theorem gE_symm_apply (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (v : (VS D).V) : (gE hsE hu σ).symm v = gF D F0 sE u σ.symm v := rfl

theorem gF_isom (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (hσ : ∀ x y, hWb D F0 (σ x) (σ y) = hWb D F0 x y) (v w : (VS D).V) :
    (VS D).hT (gF D F0 sE u σ v) (gF D F0 sE u σ w) = (VS D).hT v w := by
  rw [gF_apply, gF_apply]
  have h1 : ∀ c x, (VS D).hT x (sE c : (VS D).V) = hWb D F0 (u x) c := by
    intro c x
    rw [PI.ScalarPairDr.W.hT_swap (VS D) (sE c : (VS D).V) x, ← hu, ← hWb_swap D F0 c (u x)]
  have h2 : ∀ c x, (VS D).hT (sE c : (VS D).V) x = hWb D F0 c (u x) := fun c x => (hu c x).symm
  have h3 : ∀ c c', (VS D).hT (sE c : (VS D).V) (sE c' : (VS D).V) = hWb D F0 c c' := by
    intro c c'
    rw [h2, u_sE hsE hu]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [h3, h1, h2]
  simp only [map_sub, LinearMap.sub_apply, hσ]
  ring

end Gamma

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (o : 𝓞 K) :
    ∃ o' : 𝓞 K, (o' : K) = star (o : K) := by
  have h1 : IsIntegral ℤ (star (o : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (o : K), h1⟩, rfl⟩

theorem exists_one {K : Type} [Field K] [NumberField K] [StarRing K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h : W →ₗ⋆[K] W →ₗ[K] K) (M : Submodule (𝓞 K) W)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h M) {z : W} (hz : z ∈ M)
    (hprim : ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) : ∃ m ∈ M, h m z = 1 := by
  classical

  have memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x := by
    intro x
    conv_lhs => rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]

  let I : Ideal (𝓞 K) :=
    { carrier := {o | ∃ m ∈ M, h m z = star (o : K)}
      add_mem' := by
        rintro a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
        refine ⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, e₁, e₂]
        show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a + b))
        rw [map_add (f := _), star_add]
      zero_mem' := ⟨0, M.zero_mem, by
        rw [map_zero, LinearMap.zero_apply]
        show (0 : K) = star (algebraMap (𝓞 K) K 0)
        rw [map_zero, star_zero]⟩
      smul_mem' := by
        rintro a b ⟨m, hm, e⟩
        refine ⟨a • m, M.smul_mem a hm, ?_⟩
        have ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m := (algebraMap_smul K a m).symm
        rw [ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]
        simp only [smul_eq_mul, starRingEnd_apply]
        show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a * b))
        rw [map_mul, star_mul'] }
  have memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K) := fun o => Iff.rfl
  by_contra hne
  push_neg at hne
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (memI 1).1 h1
    exact hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)
  obtain ⟨c, hc, hc1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top
  have hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hPne] at hc

  have hcz : (star c) • z ∈ M := by
    rw [memM]
    intro m hm
    obtain ⟨t, ht⟩ := (memM z).1 hz m hm
    obtain ⟨t', ht'⟩ := star_int t
    have e1 : h m z = star (t' : K) := by rw [ht', star_star]; exact ht.symm
    have ht'I : t' ∈ I := (memI t').2 ⟨m, hm, e1⟩
    have hcy := hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at hcy
    obtain ⟨s, hs⟩ := hcy
    obtain ⟨s', hs'⟩ := star_int s
    refine ⟨s', ?_⟩
    rw [map_smul, smul_eq_mul, e1, ← star_mul']
    change (s' : K) = _
    rw [hs']
    congr 1
  obtain ⟨o, ho⟩ := hprim _ hcz
  obtain ⟨o', ho'⟩ := star_int o
  apply hc1
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_unit_condition : RowZUnit := by
  intro D u F0 Λ hrow
  obtain ⟨_, hMU, hzM, hprim⟩ := row_lattice_mass_holds D u F0 Λ hrow
  obtain ⟨m, hm, hm1⟩ := exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim
  obtain ⟨a, haΛ, rfl⟩ := (RowMPf.mem_Mof D F0 Λ m).1 hm
  refine ⟨a, haΛ, a.2, ?_⟩
  rw [zbar, hWb_mk] at hm1
  exact hm1

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_unit_condition : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnit := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition
end
end
