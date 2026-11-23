module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacComb

variable {D : D7}

theorem eq_zero_of_isHalf_zero {m n : ℕ} {x : Mx D m n} (hx : IsHalf (0 : AE D) x) : x = 0 := by
  ext i j
  have := hx i j
  simp at this
  simpa using this.symm

theorem isHalf_zero_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := by
  intro i j
  simp

theorem heisenbergSymplecticForm_zero_right_eq_zero (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem heisO_zero_eq_self (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, heisenbergSymplecticForm_zero_right_eq_zero]

theorem heisenbergTranslationCombination_single_one_eq_translate (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold GlobalTheory.SeeSaw.comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem isFinComb_single_zero {S T : HSp D} : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j
  simp [Matrix.map]

theorem vacuum_isCombOf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (p : Pair T) : IsCombOf W (FinDatum.vacuum G t p) (Finsupp.single 0 1) := by
  refine ⟨isFinComb_single_zero, ?_, ?_⟩
  · intro u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    exact isHalf_zero_zero _
  · have he : (FinDatum.vacuum G t p).e = 0 := rfl
    intro f₀ _ _
    show AllSome _ _
    rw [heisenbergTranslationCombination_single_one_eq_translate, heisO_zero_eq_self]
    refine ⟨⟨(LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS p) (G.pT p) => ℂ) 0).smulRight f₀, ?_, ?_, ?_⟩, ?_⟩
    · intro Φ _ x hx
      obtain rfl := eq_zero_of_isHalf_zero hx
      simp [heisO_zero_eq_self]
    · intro Φ _ y hy
      have hy0 : IsHalf (0 : AE D) y := by rw [he, map_zero] at hy; exact hy
      obtain rfl := eq_zero_of_isHalf_zero hy0
      simp [heisO_zero_eq_self, heisenbergSymplecticForm_zero_right_eq_zero]
    · have h0 : halfInd (0 : AE D) (latO (G.pS p) (G.pT p) ↑(G.latS p) ↑(G.latT p) fun _ => True) 0 = 1 := by
        rw [halfInd, if_pos ⟨zero_mem _, isHalf_zero_zero _⟩]
      rw [he]
      simp [h0]
    · intro Tm hT
      have := hT.vac
      rw [one_smul] at this
      exact this.symm

end GlobalTheory.VacComb


open GlobalTheory.VacComb in
theorem GlobalTheory.VacComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  exact fun t j => vacuum_isCombOf _ t _
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowVal

theorem hasLoc_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  intro D T L sc G t B j hj x g ⟨e, he, hs, hg⟩
  refine ⟨e, he, ?_, fun w => by rw [map_inv, map_inv, hg w]⟩
  intro i k
  set c := e + Formalism.L2.Theta.cA D e
  have hinv : Formalism.L2.Theta.mt _ x⁻¹ * Formalism.L2.Theta.mt _ x = 1 := by
    simp [Formalism.L2.Theta.mt, map_inv]
  have key : Formalism.L2.Theta.mt _ x⁻¹ - 1 = -(Formalism.L2.Theta.mt _ x⁻¹ * (Formalism.L2.Theta.mt _ x - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
  rw [key, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hs l k]

end GlobalTheory.RowVal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal.NIterLin

section
variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quot_sum {I : Type} (S : Finset I) (x : I → ℂ) (F : I → G → ℂ) (z : I → ℂ)
    (hF : ∀ n ∈ S, IsQuotIntL1 μR μG (F n) (z n)) :
    IsQuotIntL1 μR μG (fun g => ∑ n ∈ S, x n * F n g) (∑ n ∈ S, x n * z n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun g : G => ∑ n ∈ (∅ : Finset I), x n * F n g) = 0 := by funext g; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := (hF a (Finset.mem_insert_self _ _)).smul (x a)
    have h2 := ih (fun n hn => hF n (Finset.mem_insert_of_mem hn))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext g
    simp [Finset.sum_insert ha]
end

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
  {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i))

theorem lin (l : List ι) : ∀ (h : ∀ i, H i) (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ),
    (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n) := by
  induction l with
  | nil =>
    intro h I S x z q hq
    simp only [NIter] at hq ⊢
    exact Finset.sum_congr rfl fun n hn => by rw [hq n hn]
  | cons i l ih =>
    intro h I S x z q hq
    classical
    simp only [NIter] at hq ⊢
    let F : I → H i → ℂ := fun n => if hn : n ∈ S then Classical.choose (hq n hn) else 0
    have hF : ∀ n ∈ S, IsQuotIntL1 (ρ i) (μ i) (F n) (z n) ∧ ∀ g, NIter ρ μ (q n) l (Function.update h i g) (F n g) := by
      intro n hn
      simp only [F, dif_pos hn]
      exact Classical.choose_spec (hq n hn)
    refine ⟨fun g => ∑ n ∈ S, x n * F n g, quot_sum S x F z fun n hn => (hF n hn).1, fun g => ?_⟩
    exact ih (Function.update h i g) I S x (fun n => F n g) q fun n hn => (hF n hn).2 g

theorem congr (l : List ι) : ∀ (h : ∀ i, H i) (q q' : (∀ i, H i) → ℂ) (z : ℂ),
    (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  induction l with
  | nil =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    rw [hz]
    exact hq h fun _ _ => rfl
  | cons i l ih =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    obtain ⟨f, hf, hf'⟩ := hz
    refine ⟨f, hf, fun g => ih (Function.update h i g) q q' (f g) (fun g' hg' => hq g' fun j hj => ?_) (hf' g)⟩
    have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun e => hj (List.mem_cons_of_mem _ e)
    rw [hg' j hjl, Function.update_of_ne hji]

end GlobalTheory.RowVal.NIterLin

theorem GlobalTheory.RowVal.niter_lin_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  intro ι _ H _ _ R ρ μ l h
  exact ⟨fun I S x z q hq => GlobalTheory.RowVal.NIterLin.lin ρ μ l h I S x z q hq,
    fun q q' z hq hz => GlobalTheory.RowVal.NIterLin.congr ρ μ l h q q' z hq hz⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TiltUnique

theorem tilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  intro D T L sc G j hj δ δ' h h'
  rcases Nat.even_or_odd j with he | ho
  · rw [h.2.1 he, h'.2.1 he]
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := ho
    have h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨x1, x2, x3⟩ := h.2.2 _ hj h₂
    obtain ⟨y1, y2, y3⟩ := h'.2.2 _ hj h₂
    have k := (rowJac G j hj _ h₂).sum_eq_one
    have e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0 := x1.trans y1.symm
    have eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX := x2.trans y2.symm
    have eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY := x3.trans y3.symm
    have hm : mt _ δ = mt _ δ' := by
      rw [← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]
      rw [← k]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.TiltUnique
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def rowN (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then GlobalTheory.MixPer.flagN (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega))
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then GlobalTheory.MixPer.flagN (besDecAt G j _ h') else ⊥

def rowEmb (j : ℕ) : GA D (G.V (.top j)) →* GA D (G.V (.grid D.R.m j)) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)).emb0
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then
    GlobalTheory.MixPer.embA (besDecAt G j _ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) else 1

theorem rowGrp_eq (j : ℕ) : rowGrp G j = rowN G j ⊔ (rowEmb G j).range := by
  unfold rowGrp rowN rowEmb
  split_ifs
  · rfl
  · rfl
  · simp

def prSet (j : ℕ) (b : GfC (G.V (.grid D.R.m j))) : Set (GfC (G.V (.top j))) :=
  {g | ∃ n ∈ rowN G j, (b.1)⁻¹ * (n * rowEmb G j g.1) * b.1 ∈ latGrp G j}

end GlobalTheory.CellMass
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem defTot_smul {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (c : ℂ) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M (c • σ) τ φ F = c * defTot t S M σ τ φ F := by
  unfold defTot
  rw [Finsupp.sum_smul_index (by intro P; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring



theorem valAt_of_steps (ch : Choice R) (s : ℤˣ) (hFl : FlatAt ch s) (hT : TensAt ch) (hV : VolAt ch) (hW : WtAt ch s)
    (hFo : FockAt ch) (hB : BasicAt ch) (hO : OneAt ch) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a)) : ValAt ch s := by
  obtain ⟨z1, hz1, hFl⟩ := hFl
  obtain ⟨z2, hz2, hFo⟩ := hFo
  obtain ⟨hBa, hBf, hBM, hBM', hBgood, hBgood', hBc⟩ := hB
  refine ⟨fun t => z1 t * z2 t, fun t => Subgroup.mul_mem _ (hz1 t) (hz2 t), ?_⟩
  intro ρ μ hρμ P p hp
  obtain ⟨c0, hc0⟩ := hW ρ μ hρμ
  obtain ⟨C, hCr, hC⟩ := hFl P.2 p hp
  obtain ⟨σ₀, hσ₀⟩ := hFo C hCr P.1
  refine ⟨c0 • σ₀, ?_⟩
  intro t a τ hτ M hM β hβ b hb M' τ' hM' hτ' y
  obtain ⟨cc, hcc⟩ := hBc t (ch.Phi a) β τ' hτ'
  obtain ⟨ζ, hζ, hid⟩ := hC t (ch.Phi a) τ hτ M hM β b hb τ' cc hτ' hcc
  have hζ' : ζ = ((z1 t : ℂˣ) : ℂ)⁻¹ := hζ (hO t _ β hβ)
  obtain ⟨sc, hsc, hwx⟩ := hc0 t (ch.Phi a) β b hb M M' hM hM'
  have hgood : ∀ d ∈ τ'.support, Good ch.W (combC ch.W (cc d) C) (combR ch.rm (cc d)) := fun d hd =>
    hBgood' C hCr (cc d) (fun j hj => ((hcc d hd).1 ⟨j, hj⟩).1)
  have h1 : tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) = ζ * τ'.sum fun d x =>
      x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    have key := hT t M (hBM t M hM) (colFn ch a) (formTop ch t y) (hBa a) (hBf t y)
      ((SchRow ch.G × SchDown ch.G t) ⊕ PureDat ch.G t) (τ.support.disjSum τ'.support)
      (Sum.elim (fun d => τ d) (fun d => -ζ * τ' d))
      (Sum.elim (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b)) (fun d => combC ch.W (cc d) C))
      (Sum.elim Prod.fst (fun d => combR ch.rm (cc d))) ?_ ?_ P.1
    · rw [Finset.sum_disjSum] at key
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib] at key
      unfold tot
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      linear_combination key
    · rintro (d | d) hd
      · exact hBgood t (ch.Phi a) τ hτ M hM d (Finset.inl_mem_disjSum.1 hd) P.2 (p * b)
      · exact hgood d (Finset.inr_mem_disjSum.1 hd)
    · intro u y'
      have e := hid u y'
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum] at e
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib]
      rw [e]
      ring
  have h2 : (τ'.sum fun d x => x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y)) =
      sProd D sc * τ'.sum fun d x => x * per ch.W M' t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    rw [Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hV t M M' sc (hBM t M hM) (hBM' t _ β M' hM') hsc (colFn ch a) (formTop ch t y) (hBa a) (hBf t y) _ _ (hgood d hd) P.1]
    ring
  have h3 := hσ₀ t a β M' (hBM' t _ β M' hM') (hS t a) τ' cc hτ' hcc y
  rw [h1, h2, h3, defTot_smul, hζ', Units.val_mul, mul_inv]
  linear_combination (((z1 t : ℂˣ) : ℂ)⁻¹ * ((z2 t : ℂˣ) : ℂ)⁻¹ *
    defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) * hwx

end

theorem valAt_big : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch →
    (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s => valAt_of_steps ch s⟩⟩

end GlobalTheory.RowVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowCombGood

theorem comb_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro C hC c _
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hL := s.core.lev
  refine ⟨fun j hje hj => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := D.R.m_even
    obtain ⟨l, hl⟩ := hje
    obtain ⟨hv, hs⟩ := hC j ⟨l, hl⟩ hj
    have h1 : IsBiTheta ch.W.ψ _ _ _ (C j) :=
      GlobalTheory.FrComb.biTheta_of_vac (node_isV ch.G hL (X := .top j) (show j ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).sd hv hs
    exact GlobalTheory.FrCombAny.biTheta_biComb D _ hψ _ _ _ _ h1 _ _
  · exact GlobalTheory.CombThetaAny.main D _ hψ _ _ _ _ (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.RowCombGood
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowVal

theorem placeIdem_eq_under_of_idemAt {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : Formalism.L2.NTheta.IsIdemAt e P) {v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v' ε)
    (hs : e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) : v' = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h1, h2, -⟩ := h.1
  have hm : e * (e + cA D e) = e := by rw [mul_add, h1, h2, add_zero]
  by_contra hne
  have h0 := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (e + cA D e) P
  rw [hm, hs, h0, mul_zero, (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h).2.1] at h3
  exact one_ne_zero h3

theorem base_mt_mulVec_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  intro D T L sc G t B b hb v hv y hy
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, -⟩ := hb.1
  have hkill : ∀ PP ∈ locPl G t, ∀ a ∈ idAt D (· = v), (es PP + cA D (es PP)) * a = 0 := by
    intro PP hPP a ha
    obtain ⟨-, -, v', ε, hε, hs⟩ := (hes PP hPP).1
    have hv' : v' = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := placeIdem_eq_under_of_idemAt (hes PP hPP) hε hs
    rw [hs]
    apply (GlobalTheory.FinPl.placeIdem_acts D v' ε hε).2
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
    refine ⟨ha.1, fun w hw => ha.2 w ?_⟩
    intro h
    apply hw
    intro hwv'
    exact hv PP hPP (hv'.symm.trans (hwv'.symm.trans h))
  have hz : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i ∈ idAt D (· = v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hE : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i =
      ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) * ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hsupp i j]
  have h0 : (Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y = 0 := by
    funext i

    rw [hE i, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_eq_zero fun PP hPP => hkill PP hPP _ (hz i)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

end GlobalTheory.RowVal
end
end
