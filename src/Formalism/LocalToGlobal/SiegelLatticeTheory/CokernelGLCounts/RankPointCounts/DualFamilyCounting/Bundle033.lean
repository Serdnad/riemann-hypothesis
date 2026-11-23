module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolOrdV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ¬ TypAt X v →
    localVolumeUnit X ψ v / ZZX X u u' ψ v =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))

def VolTypV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → ∀ v : PlX X, TypAt X v → localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))

def OmV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    (omAt X.B.I.cm.sig X.B.I.J ψ v ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
        Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) *
        aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def CondAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

def DiffProd : Prop :=
  HasProd (fun v : PlX X => absV v (dV v)) (|(NumberField.discr X.B.I.F : ℝ)|⁻¹)

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def cntGe {n : ℕ} (e : Fin n → ℕ) (v : ℕ) : ℕ := (Finset.univ.filter fun i => v ≤ e i).card

theorem cntGe_succ {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    cntGe e (v + 1) + ∑ i, min (e i) v = ∑ i, min (e i) (v + 1) := by
  unfold cntGe
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem cntGe_eq {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) (v : ℕ) :
    cntGe e v = cntGe e' v := by
  cases v with
  | zero => simp [cntGe]
  | succ w =>
    have h1 := cntGe_succ e w
    have h2 := cntGe_succ e' w
    rw [H w, H (w + 1)] at h1
    omega

theorem card_eq_val {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    (Finset.univ.filter fun i => e i = v).card = cntGe e v - cntGe e (v + 1) := by
  have key : cntGe e v = (Finset.univ.filter fun i => e i = v).card + cntGe e (v + 1) := by
    unfold cntGe
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  omega

theorem exists_perm_of_min {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e' (σ i) = e i := by
  classical
  have hc : ∀ v, (Finset.univ.filter fun i => e i = v).card =
      (Finset.univ.filter fun i => e' i = v).card := by
    intro v
    rw [card_eq_val, card_eq_val, cntGe_eq e e' H, cntGe_eq e e' H]
  refine ⟨Equiv.ofFiberEquiv (f := e) (g := e') fun v => Fintype.equivOfCardEq ?_,
    fun i => Equiv.ofFiberEquiv_map _ i⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  convert hc v

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isJordanIn_perm {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (hb : IsJordanIn h X L 𝔭 b a) (σ : Equiv.Perm (Fin (finrank K X))) :
    IsJordanIn h X L 𝔭 (b ∘ σ) (a ∘ σ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  have hr : Set.range (b ∘ σ) = Set.range b := σ.surjective.range_comp b
  refine ⟨fun i => h1 _, ?_, fun i j hij => h3 _ _ (σ.injective.ne hij), fun i => h4 _,
    fun i => h5 _⟩
  rw [hr]
  exact h2

theorem nondegOn_orth {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUW : IsCompl U (orthK h U)) : NondegOn h (orthK h U) := by
  intro x hx hxy
  apply hnd
  intro v
  have hv : v ∈ U ⊔ orthK h U := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add (f := _), hxy w hw, add_zero]
  have h1 : h u x = 0 := by
    have hx' := hx
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
    exact hx' u hu
  rw [← hs.eq u x, h1, map_zero]

theorem integral_of_fib (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h T := by
  intro x hx y hy
  rw [← Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF (K := K) (F := F) (1 : Submodule (𝓞 K) K),
    Submodule.mem_iInf]
  rintro ⟨𝔭, h𝔭⟩
  have hne := hfib 𝔭 h𝔭
  unfold fibP at hne
  obtain ⟨⟨Λ, _, hdual, _, hΛT⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have hsub : ∀ z ∈ T, z ∈ Λ := fun z hz =>
    (Submodule.mem_inf.1 (hΛT.symm ▸ Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 T hz :
      z ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K))).1
  have hyd : y ∈ dualF h 𝔭 Λ := by
    rw [hdual]
    exact hsub y hy
  exact hyd x (hsub x hx)

theorem genus_of_fib (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    {T : Submodule (𝓞 K) V} (hT : IsLatIn (orthK h U) T)
    (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T := by
  intro 𝔭 h𝔭
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs
        (nondegenerate_of hs hnd) hΛ₀.1 hΛ₀.2.1 }
  have hT₀ : IsLatIn (orthK h U) (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) :=
    isLatIn_cut hΛ₀full _
  have hrefl : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))
      (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) := fun 𝔮 _ =>
    ⟨1, (isomFix h U).one_mem, by ext z; simp [Formalism.HermitianLatticesTheory.gmap]⟩
  have hfib₀ : ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal →
      fibP h U 𝔮 M (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) ≠ 0 := fun 𝔮 h𝔮 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hrefl h𝔮
  have hint := integral_of_fib hF hs hnd hUc hM hT hfib
  have hint₀ := integral_of_fib hF hs hnd hUc hM hT₀ hfib₀
  have hnd' := nondegOn_orth hs hnd hUc
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) _ hnd' hT₀ hint₀ 𝔭 h𝔭
  obtain ⟨b', a', hb'⟩ := (h1 K F V hK hF h hs).1 (orthK h U) T hnd' hT hint 𝔭 h𝔭
  obtain ⟨e₀⟩ := ((h6 K F V hK hF h hs hnd U hUc M _ hM hT₀ 𝔭 h𝔭).1 (hfib₀ 𝔭 h𝔭)).1
  obtain ⟨e⟩ := ((h6 K F V hK hF h hs hnd U hUc M T hM hT 𝔭 h𝔭).1 (hfib 𝔭 h𝔭)).1
  have hmin := h2 K F V V hK hF h h hs hs (orthK h U) (orthK h U) _ T hT₀ hT 𝔭 h𝔭 b a b' a'
    hb hb' ⟨e₀.symm.trans e⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_min (fun i => vF 𝔭 (a i)) (fun i => vF 𝔭 (a' i)) hmin
  exact hI K F V hK hF h hs hnd U hUc hpos _ T hT₀ hT 𝔭 h𝔭 b a (b' ∘ σ) (a' ∘ σ) hb
    (isJordanIn_perm hb' σ) (fun i => (hσ i).symm)

end Formalism.L2.SG.Pf.G8
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gC {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℂ :=
  if c.val < D.R.k then 1 else -(1 / ((Formalism.L2.SG.RealObj.Tw u : ℝ) : ℂ))

def RowParseval : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x y : (VS D).V),
    (∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) →
    (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    ∀ v : InfinitePlace X.B.I.F,
      ∑ c, rowV X u x v c * star (rowV X u y v c) * gC u c = X.B.I.φ v (X.ιE.symm ((VS D).hT x y))

def RowRank : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS),
    Nonempty (Module.Basis (Fin (Module.finrank ℚ D.host.E * (D.R.k + 1))) ℤ ((aaLbS X b).restrictScalars ℤ))

def TraceRe : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : D.host.E),
    ∑ v : InfinitePlace X.B.I.F, (X.B.I.φ v (X.ιE.symm t)).re = ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) / 2

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_add_l {n : ℕ} (ε : Fin n → Bool) (x y z : Fin n → ℂ) : hJ ε (x + y) z = hJ ε x z + hJ ε y z := by
  first
    | simp only [hJ, star_add, Matrix.add_dotProduct]
    | simp only [hJ, star_add, add_dotProduct]
    | simp [hJ, Matrix.add_dotProduct]
    | simp [hJ, add_dotProduct]

theorem hJ_conj' {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h, mul_comm]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem emb_star (v : InfinitePlace X.B.I.F) (t : D.host.E) :
    embS D (X.pl v) (star t) = star (embS D (X.pl v) t) := by
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ t
    | (simp only [Formalism.MainNotions.S.embS]; exact NumberField.IsCMField.complexEmbedding_complexConj _ t)
    | (haveI := D.host.isCMField_hostE
       rw [show (star t : D.host.E) = NumberField.IsCMField.complexConj D.host.E t from rfl]
       exact NumberField.IsCMField.complexEmbedding_complexConj _ _ t)
    | (haveI := D.host.isCMField_hostE
       exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embS D (X.pl v)) t)

theorem rowV_add (x y : (VS D).V) : rowV X u (x + y) = rowV X u x + rowV X u y := by
  funext v j
  have hc : X.crd (x + y) = X.crd x + X.crd y := by
    first
      | exact Formalism.L2.SG.Pf.Vanish2.crd_add X x y
      | exact Formalism.L2.SG.HidaSetting.crd_add X x y
      | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf])
  have hr : rv X.B.I v (X.crd x + X.crd y) = rv X.B.I v (X.crd x) + rv X.B.I v (X.crd y) := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [rowV, Pi.add_apply, hc, hr]
  split_ifs <;> exact hJ_add_l _ _ _ _

theorem rowV_zero : rowV X u 0 = 0 := by
  have h := rowV_add X u 0 0
  rw [add_zero] at h
  simpa using h

theorem rowV_neg (x : (VS D).V) : rowV X u (-x) = -rowV X u x := by
  rw [eq_neg_iff_add_eq_zero, add_comm (rowV X u (-x)), ← rowV_add, add_neg_cancel, rowV_zero]

theorem rowV_sub (x y : (VS D).V) : rowV X u (x - y) = rowV X u x - rowV X u y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rowV_add, rowV_neg]

def rowHom : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
  AddMonoidHom.mk' (rowV X u) (rowV_add X u)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowBlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS),
    Countable (cLat X u (Sum.inl (Sum.inr b))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inr b)))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
