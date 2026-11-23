module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle007
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SysOfStab

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma pos_iff (γ : GL (Fin 2) F) : Pos (toInf γ) ↔ TP γ.val.det := by
  have h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det
      = rhom γ.val.det := by
    rw [RingHom.map_det]; rfl
  unfold Pos TP
  rw [h]
  rfl

lemma scal_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext1
  exact ((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm

def Rel (g g' : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g' * u

lemma tp_mul {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) : TP (γ * γ').val.det := by
  rw [← pos_iff] at h h' ⊢
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1

lemma tp_inv {γ : GL (Fin 2) F} (h : TP γ.val.det) : TP (γ⁻¹).val.det := by
  rw [← pos_iff] at h ⊢
  rw [map_inv]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1

lemma tp_one : TP (1 : GL (Fin 2) F).val.det := by
  rw [← pos_iff, map_one]
  intro v
  simp

lemma sl_mul (k : ℕ) {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) (f : Hn F → ℂ) :
    sl k (toInf (γ * γ')) f = sl k (toInf γ') (sl k (toInf γ) f) := by
  rw [← pos_iff] at h h'
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1

lemma sl_one (k : ℕ) (f : Hn F → ℂ) : sl k (toInf (1 : GL (Fin 2) F)) f = f := by
  have h := (pos_iff (1 : GL (Fin 2) F)).2 tp_one
  rw [map_one]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2

lemma Rel.symm {g g' : GL (Fin 2) (Af F)} {γ : GL (Fin 2) F} (h : Rel g g' γ) : Rel g' g γ⁻¹ := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  refine ⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩
  have e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹ := by
    rw [e]; group
  rw [e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc,
    scal_comm]
  group

lemma Rel.trans {g g' g'' : GL (Fin 2) (Af F)} {γ γ' : GL (Fin 2) F} (h : Rel g g' γ) (h' : Rel g' g'' γ') :
    Rel g g'' (γ' * γ) := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  obtain ⟨hγ', z', u', hu', e'⟩ := h'
  refine ⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩
  rw [map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]
  group

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  intro F _ _ _ k Y f hcov hf
  let P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop := fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ
  let y : GL (Fin 2) (Af F) → (Af F)ˣ := fun g => Classical.epsilon (P g)
  have hy : ∀ g, P g (y g) := by
    intro g
    apply Classical.epsilon_spec (p := P g)
    obtain ⟨γ, hγ, y, hyY, u, hu, e⟩ := hcov g
    exact ⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩
  have hyeq : ∀ g g' γ, Rel g g' γ → y g = y g' := by
    intro g g' γ h
    have : P g = P g' := by
      funext x
      exact propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩
    simp only [y, this]
  choose c hc using fun g => (hy g).2
  let Ψ : GL (Fin 2) (Af F) → Hn F → ℂ := fun g => sl k (toInf (c g)) (f (y g))
  have key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g := by
    intro g g' γ h
    have h1 : Rel g (aff (y g) 0) (c g' * γ) := by
      rw [hyeq g g' γ h]; exact h.trans (hc g')
    have h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹) := (hc g).symm.trans h1
    have h3 := (hf _ (hy g).1).2.2 _ h2
    simp only [Ψ]
    rw [← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]
    conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]
  refine ⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩
  · have h := (hf _ (hy g).1).1
    exact ((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · have h := (hf _ (hy g).1).2.1
    exact ((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · exact key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
  · have := key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩
    rw [← this, sl_one]
  · have := key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1
      ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
    rw [← this, sl_one]
  · obtain ⟨hγ, z, u, hu, e⟩ := hc g
    exact ⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩

end GlobalTheory.HilbertThetaSeries.SysOfStab

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftSmooth

open Matrix

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def PSet (F : Type) [Field F] : Set (TR.Lie F 2) := {x | ∀ v, 0 < (Matrix.of x).det v}

theorem isOpen_PSet : IsOpen (PSet F) := by
  have : PSet F = ⋂ v : InfinitePlace F, (fun x : TR.Lie F 2 => (Matrix.of x).det v) ⁻¹' Set.Ioi 0 := by
    ext x; simp [PSet]
  rw [this]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_Ioi.preimage ((continuous_apply v).comp TR.contDiff_det.continuous)

theorem isUnit_of_mem_PSet {x : TR.Lie F 2} (hx : x ∈ PSet F) : IsUnit (Matrix.of x) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Pi.isUnit_iff.2 fun v => (hx v).ne'.isUnit)

theorem pos_one : Pos (1 : GL (Fin 2) (InfinitePlace F → ℝ)) := fun v => by simp

theorem key (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) :
    ∃ f : Hn F → ℂ, Hol f ∧ f (fun _ => UpperHalfPlane.I) = φ g ∧
      ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
  set gi := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set gf := Matrix.GeneralLinearGroup.map (pFin F) g
  obtain ⟨τ, hτ⟩ := (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2 gi
  have hdec := (GlobalTheory.T.rational_GL2_infinite_finite_factor F τ).1
  set M := toInf τ * gi
  set f := sl k M (Ψ (toFin τ * gf))
  have hf : Hol f := ((GlobalTheory.HilbertThetaSeries.HolKeep.main F k (Ψ (toFin τ * gf)) (Ψ (toFin τ * gf)) 1 (hΨ _) (hΨ _)).2.2.2.2.2 M hτ).2
  have hmain : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
      φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I := by
    intro u hu
    have hc := GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k M u (Ψ (toFin τ * gf)) hτ hu
    have e : ratGL F 2 τ * (g * TR.infGL F 2 u) = TR.infGL F 2 (M * u) * finGL F 2 (toFin τ * gf) := by
      rw [hdec]
      refine TR.ga_ext ?_ ?_ <;> simp [map_mul, gi, gf, M, mul_assoc]
    rw [← hL.1 τ, e, hL.2 _ hc.1, hc.2.2.2.1]
  refine ⟨f, hf, ?_, hmain⟩
  have h1 := hmain 1 pos_one
  rw [map_one, mul_one] at h1
  rw [h1, (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k 1 1 f pos_one pos_one).2.2.2.2.2]

theorem chart_eq (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (hΨ : ∀ g, Hol (Ψ g))
    (hL : IsLift k Ψ φ) (g : GA F 2) (f : Hn F → ℂ)
    (hfe : ∀ u : GL (Fin 2) (InfinitePlace F → ℝ), Pos u →
        φ (g * TR.infGL F 2 u) = sl k u f fun _ => UpperHalfPlane.I)
    (A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ)
    (hA : ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I)
    {y : TR.Lie F 2} (hy : y ∈ PSet F) : TR.chart φ g y = A y := by
  obtain ⟨w, hw⟩ := isUnit_of_mem_PSet hy
  have e : y = TR.toL w.val := hw.symm
  subst e
  have hpw : Pos w := hy
  rw [TR.chart_val, hfe w hpw, hA w hpw]

end GlobalTheory.HilbertThetaSeries.LiftSmooth

open GlobalTheory.HilbertThetaSeries.LiftSmooth in
theorem GlobalTheory.HilbertThetaSeries.lift_smooth_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  intro F _ _ _ k Ψ φ hΨ hL
  classical
  have hsm : φ ∈ TR.Sm F 2 := by
    intro g
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨u, hu⟩ := id hx
    have ex : x = TR.toL u.val := hu.symm
    obtain ⟨f, hf, -, hfe⟩ := key k Ψ φ hΨ hL (g * TR.infGL F 2 u)
    obtain ⟨A, hA1, hA2, -⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    set L := TR.lmul (TR.toL (u⁻¹).val)
    refine ⟨L ⁻¹' PSet F, isOpen_PSet.preimage L.continuous, ?_, ?_⟩
    · show ∀ v, 0 < (Matrix.of (L x)).det v
      intro v
      have : Matrix.of (L x) = 1 := by
        subst ex
        show ((u⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix _ _ _) * u.val = 1
        simp
      rw [this]; simp
    · refine (hA2.comp_inter L.contDiff.contDiffOn).congr ?_
      intro y hy
      have hy1 : IsUnit (Matrix.of y) := hy.1
      obtain ⟨w, hw⟩ := hy1
      have ey : y = TR.toL w.val := hw.symm
      have hLy : L y = TR.toL (u⁻¹ * w).val := by subst ey; rfl
      have hpos : Pos (u⁻¹ * w) := by
        intro v; have := hy.2 v; rw [hLy] at this; exact this
      simp only [Function.comp_apply]
      rw [hLy, hA1 _ hpos, ← hfe _ hpos, ey, TR.chart_val, mul_assoc, ← map_mul, mul_inv_cancel_left]
  refine ⟨hsm, fun v => ?_⟩
  have hD : ∀ g, ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ,
      TR.chart φ g =ᶠ[nhds (TR.oneL F 2)] A ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1))) =
        Complex.I * k * φ g ∧
      fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 0 (Pi.single v 1))) -
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 1 (Pi.single v 1))) =
        Complex.I * (fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 0 1 (Pi.single v 1))) +
          fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single 1 0 (Pi.single v 1)))) := by
    intro g
    obtain ⟨f, hf, hfg, hfe⟩ := key k Ψ φ hΨ hL g
    obtain ⟨A, hA1, -, hA3⟩ := GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering F k f hf
    obtain ⟨h1, h2⟩ := hA3 v _ fun _ _ => rfl
    refine ⟨A, ?_, ?_, h2⟩
    · have hmem : TR.oneL F 2 ∈ PSet F := fun w => by simp
      exact Filter.eventually_of_mem (isOpen_PSet.mem_nhds hmem) fun y hy => chart_eq k Ψ φ hΨ hL g f hfe A hA1 hy
    · rw [h1, hfg]
  constructor
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, h1, -⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = (Complex.I * k) * φ g
    rw [TR.lieD, TR.lieD, hA.fderiv_eq, h1]
  · refine Subtype.ext (funext fun g => ?_)
    obtain ⟨A, hA, -, h2⟩ := hD g
    show TR.lieD _ φ g - TR.lieD _ φ g = Complex.I * (TR.lieD _ φ g + TR.lieD _ φ g)
    rw [TR.lieD, TR.lieD, TR.lieD, TR.lieD, hA.fderiv_eq, h2]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ), (∀ g, Hol (Ψ g)) → IsLift k Ψ φ → ∃ h : φ ∈ TR.Sm F 2, ∀ v, TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k) • (⟨φ, h⟩ : TR.Sm F 2) ∧ TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 ⟨φ, h⟩) := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | exact GlobalTheory.HilbertThetaSeries.lift_smooth_lowering | (intros; apply GlobalTheory.HilbertThetaSeries.lift_smooth_lowering <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem et_pow_den_eq_one {F : Type} [Field F] [NumberField F] (y : F) :
    et y ^ (Algebra.trace ℚ F y).den = 1 := by
  unfold et
  set q : ℚ := Algebra.trace ℚ F y
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℕ) : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) this
  have : ((q.den : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← h]; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem padic_norm_et_eq_one {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (y : F) :
    ‖ι.symm (et y)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (et_pow_den_eq_one y)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Rat.den_nz _)).1 h

theorem QF_mulVec_of_iso {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {G S : Matrix κ κ ℤ} (h : Sᵀ * G * S = G) (x : κ → F) :
    QF G (S.map (Int.cast : ℤ → F) *ᵥ x) = QF G x := by
  have h' : (S.map (Int.cast : ℤ → F))ᵀ * G.map (Int.cast : ℤ → F) * S.map (Int.cast : ℤ → F)
      = G.map (Int.cast : ℤ → F) := by
    have := congrArg (fun A : Matrix κ κ ℤ => A.map (Int.castRingHom F)) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  unfold QF BF
  congr 1
  conv_rhs => rw [← h']
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

theorem good_mul_et_QF : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  intro F _ _ p hp ι δ hδ κ _ _ G S t hL Φ hΦ b hb
  obtain ⟨⟨N, hN, hNp, hsupp, hper⟩, hS, hint, h0⟩ := hΦ
  obtain ⟨M, hM, hMp, htr⟩ := (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).2.2.1 b hb
  obtain ⟨hadd, hsmul, -, hI, hLL, haL, het, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hL.pos
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  have hnat : ∀ (n : ℕ) (l : κ → F), l ∈ LL F κ → (n : F) • l ∈ LL F κ := by
    intro n l hl
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hl n
  refine ⟨⟨N * N * M, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hNp) hMp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 (hsupp x (left_ne_zero_of_mul hx))
    refine (haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  · intro x l' hl'
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 hl'
    have h1 : Φ (x + ((N * N * M : ℕ) : F) • l) = Φ x := by
      refine hper x _ ((haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩)
      rw [smul_smul]
      congr 1
      push_cast
      ring
    show Φ _ * _ = Φ x * _
    rw [h1]
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨y, hy, rfl⟩ := (haL _ _).1 (hsupp x hx)
    congr 1
    have hz : IsIntegral ℤ ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) :=
      ((isIntegral_natCast N).mul ((hI y hy).2 l hl)).add ((isIntegral_natCast _).mul (hI l hl).1)
    have h2 : b * QF G ((N : F)⁻¹ • y + ((N * N * M : ℕ) : F) • l) = b * QF G ((N : F)⁻¹ • y) +
        (M : F) * b * ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) := by
      rw [(hadd _ _).2, (hsmul _ y _).1, (hadd y _).1, (hsmul _ l y).1, (hsmul _ l y).2.1, (hadd l y).1]
      push_cast
      field_simp
      ring
    rw [h2, (het _ _).1, (het _ 0).2.2.1.2 (htr _ hz), mul_one]
  · intro x
    show Φ _ * _ = Φ x * _
    rw [hS, QF_mulVec_of_iso hL.iso]
  · intro x
    show ‖ι.symm (Φ x * _)‖ ≤ 1
    rw [map_mul, norm_mul, padic_norm_et_eq_one, mul_one]
    exact hint x
  · show ‖ι.symm (Φ 0 * _) - 1‖ ≤ _
    have : et (b * QF G (0 : κ → F)) = 1 := by simp [et, QF, BF]
    rw [this, mul_one]
    exact h0

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.good_mul_et_QF | exact GlobalTheory.HilbertThetaSeries.good_mul_et_QF | (intros; apply GlobalTheory.HilbertThetaSeries.good_mul_et_QF <;> assumption)
end
