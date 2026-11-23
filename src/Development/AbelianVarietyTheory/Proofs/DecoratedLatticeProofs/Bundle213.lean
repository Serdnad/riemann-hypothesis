module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7}

def tens {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ := fun t => Φ (t - b • t) * Ψ (b • t)

theorem tens_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) (t : WO S T) :
    tens b Φ Ψ t = Φ (t - b • t) * Ψ (b • t) := rfl

def tensL {S T : HSp D} (b : AE D) (Ψ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := tens b Φ Ψ
  map_add' Φ Φ' := by funext t; simp only [tens, Pi.add_apply, add_mul]
  map_smul' c Φ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

def tensR {S T : HSp D} (b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := tens b Φ Ψ
  map_add' Ψ Ψ' := by funext t; simp only [tens, Pi.add_apply, mul_add]
  map_smul' c Ψ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensL_apply {S T : HSp D} (b : AE D) (Ψ Φ : WO S T → ℂ) : tensL b Ψ Φ = tens b Φ Ψ := rfl

theorem tensR_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : tensR b Φ Ψ = tens b Φ Ψ := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def eSum (p : ι → SplitPt D k) (J : List ι) : AE D := (J.map fun i => (p i).e).sum

theorem eSum_cons (p : ι → SplitPt D k) (i : ι) (J : List ι) : eSum p (i :: J) = (p i).e + eSum p J := by
  simp [eSum]


open Classical in
def datJ (p : ι → SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}
    (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (J : List ι) (t : WO S T) : ℂ :=
  if IsHalf (eSum p J) t then (J.map fun i => Ψ i (rd (α i) (β i) t)).prod else 0

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  rw [← p.sec_one, p.pr_sec]

theorem pr_of_mul_eq_zero (p : SplitPt D k) {a : AE D} (h : p.e * a = 0) : p.pr a = 0 := by
  have := congrArg p.pr h
  rwa [map_mul, pr_e, one_mul, map_zero] at this

theorem mul_eSum (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, a * (p j).e = 0) : a * eSum p J = 0 := by
  induction J with
  | nil => simp [eSum]
  | cons j J ih =>
    rw [eSum_cons, mul_add, h j (List.mem_cons_self), ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), add_zero]

theorem eSum_mul (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, (p j).e * a = 0) : eSum p J * a = 0 := by
  rw [mul_comm]; exact mul_eSum p a J fun j hj => by rw [mul_comm]; exact h j hj

theorem eSum_idem (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup) :
    eSum p J * eSum p J = eSum p J := by
  induction J with
  | nil => simp [eSum]
  | cons i J ih =>
    rw [List.nodup_cons] at hJ
    have h1 : (p i).e * eSum p J = 0 := mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    have h2 : eSum p J * (p i).e = 0 := by rw [mul_comm, h1]
    rw [eSum_cons, add_mul, mul_add, mul_add, (p i).split.1, h1, h2, ih hJ.2, add_zero, zero_add]

theorem pr_eSum (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup)
    (i : ι) (hi : i ∈ J) : (p i).pr (eSum p J) = 1 := by
  induction J with
  | nil => simp at hi
  | cons j J ih =>
    rw [List.nodup_cons] at hJ
    rw [eSum_cons, map_add (f := _)]
    by_cases hij : i = j
    · subst hij
      rw [pr_e, pr_of_mul_eq_zero (p i) (mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)), add_zero]
    · rw [pr_of_mul_eq_zero (p i) (horth i j hij), zero_add, ih hJ.2 ((List.mem_cons.1 hi).resolve_left hij)]

end GlobalTheory.FinPl.PutIn

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGfCImg

theorem gl_mem_GfC : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfCImg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FrameGfC

theorem gl_mem_GfC : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfC
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.OffPlace

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_of_idOff (p : SplitPt D k) {a : Formalism.L2.Theta.AE D} (ha : a ∈ idOff D (· = p.v)) : p.pr a = 0 := by

  have hv : compAt D p.v a = 0 := by
    rw [idOff, Submodule.mem_iInf] at ha
    exact ha ⟨p.v, rfl⟩
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  obtain ⟨α, hα, hαv, hαw⟩ := hε
  have hparts := placeIdempotent_infinite_and_finite_components D p.v ε α hα

  have hεa : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [map_mul, hparts.1, zero_mul]
    · intro w
      rw [map_mul, hparts.2 w]
      by_cases hw : w = p.v
      · subst hw
        rw [hv, mul_zero]
      · rw [hαw w hw, TensorProduct.zero_tmul, zero_mul]

  have hea : p.e * a = 0 := by
    have : p.e * algebraMap (AF D.host.F) (AE D) ε = p.e := by
      rw [← hsum, mul_add, hee, hec, add_zero]
    rw [← this, mul_assoc, hεa, mul_zero]
  rw [← p.pr_sec (p.pr a), p.sec_pr, hea, map_zero]

theorem map_pr_of_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  intro D k _ _ _ _ p S n _ _ β κ g h
  set γ := κ * (β.gl g)⁻¹ with hγ

  have hq : (mt S γ).map (Ideal.Quotient.mk (idOff D (· = p.v))) = 1 := by
    rw [grpOff, congGrp, MonoidHom.mem_ker] at h
    have := congrArg (fun M : GL (Fin S.rank) (AE D ⧸ idOff D (· = p.v)) => M.val) h
    simpa [Formalism.L2.Theta.mt] using this

  have hγ1 : (mt S γ).map p.pr = 1 := by
    ext i j
    have hij := congrFun (congrFun hq i) j
    have hmem : mt S γ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D (· = p.v) := by
      rw [← Ideal.Quotient.eq]
      rw [Matrix.map_apply] at hij
      rw [hij, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := pr_of_idOff p hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hκ : κ = γ * β.gl g := by rw [hγ, inv_mul_cancel_right]
  have hmt : mt S κ = mt S γ * mt S (β.gl g) := by
    rw [hκ]
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  rw [hmt, Matrix.map_mul, hγ1, one_mul, β.gl_mat g]

end GlobalTheory.AdForm.OffPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSupp

theorem mxAt_of_isHalf_above : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  intro D k _ _ _ _ q m n w hw i j
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [(placeIdem_acts D q.v ε hε).1, ← heq]
  exact hw i j

end GlobalTheory.FinPl.SplitHalfSupp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

namespace GlobalTheory.FinPl

theorem movesLocal_supp_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (v : Pl D)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L (fun _ => True) ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L y hL
  have hsub : ∀ i, y i ∈ idAt D (fun _ => True) := by
    intro i
    have h := hy i
    simp only [idAt, Submodule.mem_inf] at h ⊢
    refine ⟨h.1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w trivial e he⟩
  · rintro ⟨_, h⟩
    refine ⟨hsub, fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem movesLocal : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ g : GA D S, (GlobalTheory.FinPl.Moves S g L L (fun _ => True) ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L L (· = v)) := by
  intro D S L hL g
  have hmv : ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
    intro P y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  constructor
  · intro h v y hy
    have hyT : ∀ i, y i ∈ idAt D (fun _ => True) := by
      intro i
      have h' := hy i
      simp only [idAt, Submodule.mem_inf] at h' ⊢
      refine ⟨h'.1, ?_⟩
      simp only [Submodule.mem_iInf]
      intro w
      exact absurd trivial w.2
    rw [← movesLocal_supp_iff S L hL.1 v y hy, ← movesLocal_supp_iff S L hL.1 v _ (hmv _ y hy)]
    exact h y hyT
  · intro h y hy
    have hT := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L z hL.1
    rw [hT y, hT (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w (e • y) hey).1 (hy' w trivial e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w trivial e he

end GlobalTheory.FinPl
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem extL_mem_latO : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  intro D V₀ A L S o P LA LS M hA hS hM hO u hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D A S LA LS hA hS P u] at hu
  obtain ⟨huP, huL⟩ := hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V₀ S M LS hM hS P, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hloc := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (huP i k)
  · have hy' := ((hloc V₀).2.2.2 M y hM.1).1 hy
    have hp : o.pA *ᵥ y ∈ latV A LA P := by
      refine ((hloc A).2.2.2 LA (o.pA *ᵥ y) hA.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
      · rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy'.1 k)
      · obtain ⟨LL, hLL⟩ := hO v hv
        have h1 := ((hLL (e • y)).1 (hy'.2 v hv e he)).1
        rwa [Matrix.mulVec_smul] at h1
    have h2 := huL _ hp
    change (u * o.pA) *ᵥ y ∈ latA S LS P
    rwa [← Matrix.mulVec_mulVec]

end GlobalTheory.ContrComb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ContrComb.LatT

variable {D : D7}

theorem latV_entry_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem jA_latV {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {y : Fin A.rank → AE D} (hy : y ∈ latV A LA P) : o.jA *ᵥ y ∈ latV V₀ M P := by
  have hG := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hy' := ((hG.2 A).2.2.2 LA y hLA.1).1 hy
  refine ((hG.2 V₀).2.2.2 M _ hM.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy'.1 j)
  · obtain ⟨LL, hLL⟩ := hloc v hv
    have hz := hy'.2 v hv e he
    rw [← Matrix.mulVec_smul]
    refine (hLL _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]; exact hz
    · rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]; exact zero_mem _

theorem smul_latV_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem jA_latA {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {z : Fin A.rank → AE D} (hz : z ∈ latA A LA P) : o.jA *ᵥ z ∈ latA V₀ M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hg
    have hsplit : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i) : Fin A.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_latV_mem_latA ha
      (jA_latV o hLA hM hloc (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_extR : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S)
    (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) →
    ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  intro D V₀ A L S o P LA LS M hLA hLS hM hloc u hu
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S A LS LA hLS hLA P u).1 hu
  refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S V₀ LS M hLS hM P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hu'.1 k j)
  · show (o.jA * u) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact jA_latA o hLA hM hloc (hu'.2 y hy)

end GlobalTheory.ContrComb.LatT
end
end
