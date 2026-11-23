module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7} {a b : ℕ}

def EvGood (Φ : Mx D a b → ℂ) : Prop :=
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ

theorem good_zero (S : Finset (Pl D)) (e : AE D) : Good S e (0 : Mx D a b → ℂ) := by
  intro x
  split_ifs <;> rfl

theorem good_add {S : Finset (Pl D)} {e : AE D} {Φ Ψ : Mx D a b → ℂ} (hΦ : Good S e Φ) (hΨ : Good S e Ψ) :
    Good S e (Φ + Ψ) := by
  intro x
  simp only [Pi.add_apply]
  rw [hΦ x, hΨ x]
  split_ifs with h
  · rfl
  · simp

theorem good_smul {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : Good S e Φ) :
    Good S e (c • Φ) := by
  intro x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hΦ x]
  split_ifs with h
  · rfl
  · simp

theorem evGood_zero : EvGood (0 : Mx D a b → ℂ) :=
  ⟨∅, fun S _ e _ => good_zero S e⟩

theorem evGood_add {Φ Ψ : Mx D a b → ℂ} (hΦ : EvGood Φ) (hΨ : EvGood Ψ) : EvGood (Φ + Ψ) := by
  classical
  obtain ⟨S₁, h₁⟩ := hΦ
  obtain ⟨S₂, h₂⟩ := hΨ
  exact ⟨S₁ ∪ S₂, fun S hS e he =>
    good_add (h₁ S (Finset.union_subset_left hS) e he) (h₂ S (Finset.union_subset_right hS) e he)⟩

theorem evGood_smul {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : EvGood Φ) : EvGood (c • Φ) := by
  obtain ⟨S₀, h⟩ := hΦ
  exact ⟨S₀, fun S hS e he => good_smul c (h S hS e he)⟩

theorem evGood_span {s : Set (Mx D a b → ℂ)} (hs : ∀ φ ∈ s, EvGood φ) :
    ∀ Φ ∈ Submodule.span ℂ s, EvGood Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact evGood_zero
  | add x y _ _ hx hy => exact evGood_add hx hy
  | smul c x _ hx => exact evGood_smul c hx

theorem ev_span {θ : InfFam D} (s : Set (Mx D a b → ℂ)) (hs : schwartzA θ a b = Submodule.span ℂ s)
    (h : ∀ φ ∈ s, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e φ) :
    ∀ Φ ∈ schwartzA θ a b, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ := by
  intro Φ hΦ
  rw [hs] at hΦ
  exact evGood_span h Φ hΦ

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LCfInv

variable {D : D7} {n : ℕ}

theorem fam_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {u : G D n} (hH : ∀ g, H (g * u) = H g)
    (hφ : ∀ g, φ (g * u) = φ g) (s₁ z : ℂ) (g : G D n) : fam H φ s₁ z (g * u) = fam H φ s₁ z g := by
  simp only [fam, hH, hφ]

theorem eisS_mul {f : G D n → ℂ} {u : G D n} (hf : ∀ g, f (g * u) = f g) (g : G D n) :
    eisS f (g * u) = eisS f g := by
  unfold eisS GlobalTheory.Eis.cosetSum
  refine tsum_congr fun q => ?_
  simp only [GlobalTheory.Eis.term, ← mul_assoc, hf]

theorem E_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hc : IsCont H φ s₀ U d E σ) {u : G D n} (hH : ∀ g, H (g * u) = H g) (hφ : ∀ g, φ (g * u) = φ g) (g : G D n) :
    ∀ z ∈ U, E z (g * u) = E z g := by
  have ah : AnalyticOnNhd ℂ (E · (g * u)) U := (hc.hol (g * u)).analyticOnNhd hc.isOpen
  have ag : AnalyticOnNhd ℂ (E · g) U := (hc.hol g).analyticOnNhd hc.isOpen
  obtain ⟨τ, hτ⟩ := hc.right.1
  have hx : ((max τ σ + 1 : ℝ) : ℂ) ∈ rightOf (max τ σ) := by simp
  have hxU : ((max τ σ + 1 : ℝ) : ℂ) ∈ U := hτ (rightOf_subset (le_max_left _ _) hx)
  have ev : (E · (g * u)) =ᶠ[𝓝 ((max τ σ + 1 : ℝ) : ℂ)] (E · g) := by
    filter_upwards [(isOpen_rightOf (max τ σ)).mem_nhds hx] with w hw
    have hw' : σ < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hc.eq w hw', eisS_mul (fam_mul hH hφ s₀ w)]
  exact fun z hz => ah.eqOn_of_preconnected_of_eventuallyEq ag hc.right.isPreconnected hxU ev hz

end PositivityTheory.Rg.Rsw.L.LCfInv

namespace PositivityTheory.Rg.Rsw.L

open LCfInv in
theorem cfInv : CfInv := by
  intro D n H s₀ φ U d E σ hc ε hε u hH hφ k g
  unfold cf
  congr 1
  refine circleIntegral.integral_congr hε.1.le fun z hz => ?_
  have hzU : z ∈ U := hε.2.1 (Metric.sphere_subset_closedBall hz)
  simp only [E_mul hc hH hφ g z hzU]

end PositivityTheory.Rg.Rsw.L

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh




open PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem mat_mul_inv (g : G D n) : mat g * mat g⁻¹ = 1 := by simp [mat]

theorem mat_proj (g : G D n) (v : Pl D) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 : Matrix _ _ _) =
      (mat g).map (cv D v) := rfl

theorem compInf_eq (w : InfinitePlace D.host.F) (x : AE D) :
    compInf D.host.F D.host.E w x = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem kOff_inf {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (w : InfinitePlace D.host.F) (i j : Fin (n + n)) :
    compInf D.host.F D.host.E w (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h1 := (mem_levelOff.1 hg).1
  have h2 : (mat g).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at h3
  rw [compInf_eq]
  change _ = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mat g i j) = _ from h3]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem kOff_at {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∈ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h := (mem_levelOff.1 hg).2.1 v hv
  have := congrArg (fun x => ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) x).1 : Matrix _ _ _)) h
  simp only [mat_proj, map_one, Units.val_one] at this
  have := congrFun (congrFun this i) j
  simpa using this

theorem kOff_int {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∉ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v := by
  have h := (mem_levelOff.1 hg).2.2 v hv
  have hs : ∀ y, y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v ↔
      (mat g).map (cv D v) *ᵥ y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := h
  have he : ∀ k : Fin (n + n), (Pi.single k 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      latLoc D.host.F (stdLattice D.host.E (n + n)) v := fun k => by
    rw [mem_latLoc_stdLattice]
    intro l
    by_cases e : l = k
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have hM : (mat g).map (cv D v) * (mat g⁻¹).map (cv D v) = 1 := by
    have := (RingHom.mapMatrix (cv D v)).map_mul (mat g) (mat g⁻¹)
    rw [mat_mul_inv, map_one] at this
    exact this.symm
  constructor
  · have := mem_latLoc_stdLattice.1 ((hs _).1 (he j)) i
    simpa [Matrix.mulVec_single_one] using this
  · have h2 : (mat g⁻¹).map (cv D v) *ᵥ Pi.single j 1 ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
      refine (hs _).2 ?_
      rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
      exact he j
    have := mem_latLoc_stdLattice.1 h2 i
    simpa [Matrix.mulVec_single_one] using this

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem indS_apply (S : Finset (Pl D)) (v : Pl D) : (indS S) v = if v ∈ S then 1 else 0 := rfl

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem infPart_eS (S : Finset (Pl D)) : infPart D (eS S) = 1 := by
  simp only [infPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

theorem finPart_eS (S : Finset (Pl D)) :
    finPart D (eS S) = algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) := by
  simp only [finPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem cv_eq (v : Pl D) (z : AE D) :
    cv D v z = Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _), map_add (f := _)]
  | tmul a x => rfl

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

structure SplitPkg (D : D7) (v : Pl D) where
  π : Fv D.host.F v ⊗[D.host.F] D.host.E ≃ₐ[Fv D.host.F v] Fv D.host.F v × Fv D.host.F v
  swap : ∀ y, π (sigR (Fv D.host.F v) D.sp.cm.sig y) = (π y).swap
  int : ∀ y, y ∈ intLoc D.host.F D.host.E v ↔
    (π y).1 ∈ v.adicCompletionIntegers D.host.F ∧ (π y).2 ∈ v.adicCompletionIntegers D.host.F

def PlaceEx : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ →
  ∀ r : ℕ, ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ P : SplitPkg D v,
    (∀ a : Fv D.host.F v, (∀ b ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v (a * b) = 1) ↔
      a ∈ v.adicCompletionIntegers D.host.F) ∧
    (∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 ∈ v.adicCompletionIntegers D.host.F →
      (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 ∈ v.adicCompletionIntegers D.host.F → (P.π u).2 = 1 →
      χ (ideleAt D.host.F D.host.E v u) = 1) ∧
    ∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 = (P.π u).2 → χ (ideleAt D.host.F D.host.E v u) = 1

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
end
