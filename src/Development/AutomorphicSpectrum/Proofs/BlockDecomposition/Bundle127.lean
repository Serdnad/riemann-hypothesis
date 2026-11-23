module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle115
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.TruncationHomExt
public import Mathlib.Algebra.Exact.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle116
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w'

section LES

theorem cls_congr {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}

theorem sq_mapH {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L L' σ)
    (φ' : Cx.Hom K' L' (RingHom.id R')) (ψ' : Cx.Hom K K' σ)
    (h : ∀ n x, ψ.f n (φ.f n x) = φ'.f n (ψ'.f n x)) (n : ℕ) (z : K.H n) :
    ψ.mapH n (φ.mapH n z) = φ'.mapH n (ψ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 z
  have c1 : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have c2 : L'.d n (ψ.f n (φ.f n x)) = 0 := by rw [ψ.comm, c1, map_zero]
  have c3 : K'.d n (ψ'.f n x) = 0 := by rw [ψ'.comm, hx, map_zero]
  have c4 : L'.d n (φ'.f n (ψ'.f n x)) = 0 := by rw [φ'.comm, c3, map_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx c1, CrystallineSemistableComparison.P.mapH_cls ψ n _ c1 c2, CrystallineSemistableComparison.P.mapH_cls ψ' n x hx c3,
    CrystallineSemistableComparison.P.mapH_cls φ' n _ c3 c4]
  exact cls_congr (h n x) _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_les [∀ i, Module.Flat R (N i)]
    {K L M : ι → Cx.{w} R} {K' L' M' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) (g : ∀ i, Cx.Hom (L i) (M i) (RingHom.id R))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (f' : Cx.Hom K' L' (RingHom.id R')) (g' : Cx.Hom L' M' (RingHom.id R'))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (a : ∀ i, N i → Cx.Hom (K i) K' σ) (b : ∀ i, N i → Cx.Hom (L i) L' σ) (c : ∀ i, N i → Cx.Hom (M i) M' σ)
    (hab : ∀ i n k x, (b i n).f k ((f i).f k x) = f'.f k ((a i n).f k x))
    (hbc : ∀ i n k x, (c i n).f k ((g i).f k x) = g'.f k ((b i n).f k x))
    (hL : ∀ j, Tens R (N := N) (M := fun i => (L i).H j) (M' := L'.H j) fun i n x => (b i n).mapH j x)
    (hM : ∀ j, Tens R (N := N) (M := fun i => (M i).H j) (M' := M'.H j) fun i n x => (c i n).mapH j x)
    (hadd : ∀ i j, ∃ F : N i ⊗[R] (K i).H j →+ K'.H j, ∀ n x, F (n ⊗ₜ x) = (a i n).mapH j x) :
    ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (a i n).mapH j x := by
  intro j
  choose δ hδ h0 e1 e2 e3 using fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  obtain ⟨δ', hδ', h0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have dcomm : ∀ i n k z, (a i n).mapH (k + 1) (δ i k z) = δ' k ((c i n).mapH k z) := by
    intro i n k z
    obtain ⟨m, hm, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (M i) k).1 z
    obtain ⟨y, rfl⟩ := hg i k m
    obtain ⟨x, hx⟩ := CrystallineSemistableComparison.CechClassBoundaries.conn_ex (f i) (g i) (hfg i) y hm
    have hxc := CrystallineSemistableComparison.CechClassBoundaries.conn_cyc (f i) (hf i) y x hx
    have c3 : K'.d (k + 1) ((a i n).f (k + 1) x) = 0 := by rw [(a i n).comm, hxc, map_zero]
    have c4 : M'.d k ((c i n).f k ((g i).f k y)) = 0 := by rw [(c i n).comm, hm, map_zero]
    have c5 : M'.d k (g'.f k ((b i n).f k y)) = 0 := by rw [← hbc]; exact c4
    rw [hδ i k y x hm hxc hx, CrystallineSemistableComparison.P.mapH_cls (a i n) _ x hxc c3, CrystallineSemistableComparison.P.mapH_cls (c i n) k _ hm c4,
      cls_congr (hbc i n k y) c4 c5, hδ' k _ _ c5 c3 (by rw [← hab, hx, (b i n).comm])]
  cases j with
  | zero =>
    refine tens_five (M₁ := fun _ => PUnit.{w + 1}) (M₂ := fun _ => PUnit.{w + 1}) (L₁ := PUnit.{w' + 1}) (L₂ := PUnit.{w' + 1})
      (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
      0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
      (fun _ _ _ => 0) (fun _ _ _ => 0) _ (fun i n x => (b i n).mapH 0 x) (fun i n x => (c i n).mapH 0 x)
      (fun _ _ _ => rfl) (fun i n x => ?_) (fun i n x => ?_) (fun i n x => ?_)
      (fun i y => by simp) (fun i y => ?_) (fun i => e1 i 0)
      (fun y => by simp) (fun y => ?_) (e1' 0)
      (tens_zero (fun _ => inferInstance) inferInstance _) (tens_zero (fun _ => inferInstance) inferInstance _)
      (hL 0) (hM 0) (fun i => hadd i 0)
    · have : (0 : PUnit.{w + 1} →ₗ[R] (K i).H 0) x = 0 := rfl
      simp
    · exact sq_mapH (f i) (b i n) f' (a i n) (hab i n) 0 x
    · exact sq_mapH (g i) (c i n) g' (b i n) (hbc i n) 0 x
    · constructor
      · intro h
        have : y = 0 := h0 i (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
    · constructor
      · intro h
        have : y = 0 := h0' (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
  | succ k =>
    exact tens_five (fun i => (g i).mapH k) (fun i => δ i k) (fun i => (f i).mapH (k + 1)) (fun i => (g i).mapH (k + 1))
      (g'.mapH k).toAddMonoidHom (δ' k).toAddMonoidHom (f'.mapH (k + 1)).toAddMonoidHom (g'.mapH (k + 1)).toAddMonoidHom
      (fun i n x => (b i n).mapH k x) (fun i n x => (c i n).mapH k x) _
      (fun i n x => (b i n).mapH (k + 1) x) (fun i n x => (c i n).mapH (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) k x) (fun i n x => dcomm i n k x)
      (fun i n x => sq_mapH (f i) (b i n) f' (a i n) (hab i n) (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) (k + 1) x)
      (fun i => e2 i k) (fun i => e3 i k) (fun i => e1 i (k + 1)) (e2' k) (e3' k) (e1' (k + 1))
      (hL k) (hM k) (hL (k + 1)) (hM (k + 1)) (fun i => hadd i (k + 1))

end LES

end GlobalTheory.CompanionTheory.LocBC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConePow

theorem cupPowC_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ) : cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    change (CH.mulP A).cupC (by omega) (cupPowC A (a • z) k) (a • z) =
      a ^ (k + 1) • (CH.mulP A).cupC (by omega) (cupPowC A z k) z
    rw [ih, map_smul, map_smul, LinearMap.smul_apply, pow_succ', mul_smul]

end GlobalTheory.CompanionTheory.ConePow
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRep

theorem rep_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (a b : IdF A)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (z : CH.Cn (CH.modF (U.ι ⋙ A)) j) (c : HU (sq a b) U j) :
    Rep (a.res U.ι) (b.res U.ι) z c → Rep (a.res V.ι) (b.res V.ι) (resB A h z) ((resU (sq a b) h).pull j c) := by
  rintro ⟨f, hf, hc, hz⟩
  have hf' : CH.d (U.ι ⋙ sq a b) j f = 0 := hf
  have hb : CH.d (V.ι ⋙ sq a b) j ((resU (sq a b) h).pullC j f) = 0 := by
    rw [(resU (sq a b) h).d_pullC, hf', map_zero]
  have hcl : (resU (sq a b) h).pull j c = (CH.cx (V.ι ⋙ sq a b)).cls ((resU (sq a b) h).pullC j f) hb := by
    have hc' : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf' := hc
    rw [hc']
    rfl
  exact ⟨(resU (sq a b) h).pullC j f, hb, hcl, fun s => hz (s ⋙ ObjectProperty.ιOfLE h)⟩

end GlobalTheory.CompanionTheory.ConeRep
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechRowExact

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type} (U : ι → ObjectProperty C)

theorem cosieve_capT (hU : ∀ α, Cosieve (U α)) {n : ℕ} (i : Fin n → ι) : Cosieve (capT U i) :=
  fun _ _ φ h a => hU (i a) φ (h a)

theorem capT_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capT U i T) :
    capT U (Fin.cons (α := fun _ => ι) a i) T := fun k => by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi k

def liftC (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (s : ComposableArrows C q)
    (h : capT U i (s.obj 0)) : ComposableArrows (capT U i).FullSubcategory q :=
  (capT U i).lift s fun k => cosieve_capT U hU i (s.map (homOfLE (Fin.zero_le k))) h

def ev (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (x : CH.Cn ((capT U i).ι ⋙ F) q)
    (s : ComposableArrows C q) (h : capT U i (s.obj 0)) : F.obj (s.obj (Fin.last q)) :=
  x (liftC U hU i s h)

variable {F U}

theorem ev_congr (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (f : ∀ i : Fin n → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    {i i' : Fin n → ι} (e : i = i') (s : ComposableArrows C q) (h : capT U i (s.obj 0))
    (h' : capT U i' (s.obj 0)) : ev F U hU i (f i) s h = ev F U hU i' (f i') s h' := by
  subst e; rfl

theorem ev_d (hU : ∀ α, Cosieve (U α)) {p q : ℕ} (f : ∀ i : Fin (p + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (((cechCC F U).cos q).d p f i) s h =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • ev F U hU (i ∘ k.succAbove) (f (i ∘ k.succAbove)) s (fun a => h _) := by
  have e := congrFun (congrFun (Cos.d_apply ((cechCC F U).cos q) p f) i) (liftC U hU i s h)
  refine e.trans ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  rfl

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

def hh (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (i : Fin (p + 1) → ι) :
    CH.Cn ((capT U i).ι ⋙ F) q := fun t =>
  ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (t.obj 0).obj) i)) (t ⋙ (capT U i).ι)
    (capT_cons U (hα _) (t.obj 0).property)

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d (p + 1) f = 0)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s
        (capT_cons U (hα _) fun a => h _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d (p + 1) f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_succ] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 : ∀ j : Fin (p + 2), ev F U hU _ (f ((Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) s (fun a => h' _) =
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s (capT_cons U (hα _) fun a => h _) :=
    fun j => ev_congr hU f (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {q : ℕ}
    (f : ∀ i : Fin (0 + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d 0 f = 0)
    (i : Fin (0 + 1) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d 0 f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_two] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 := ev_congr hU f (i := (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (0 + 2) → ι) ∘ (1 : Fin (0 + 2)).succAbove)
    (i' := fun _ => α (s.obj 0)) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (fun a => h' _) (fun _ => hα _)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

end GlobalTheory.CompanionTheory.CechRowExact


open GlobalTheory.CompanionTheory.CechRowExact in
theorem GlobalTheory.CompanionTheory.CechRowExact.cech_rows : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ q, ((cechCC F U).dcx.row q).ResUpTo 1 ((cechAugRowU F U).ε q) := by
  intro R _ C _ F ι U hU hc q
  choose α hα using hc
  refine ⟨(cechAugRowU F U).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩
  · rw [one_smul]
    funext s
    have h1 := congrFun (congrFun hg fun _ => α (s.obj 0)) (liftC U hU _ s fun _ => hα _)
    exact h1
  · refine ⟨fun s => ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _), ?_⟩
    rw [one_smul]
    funext i t
    exact (cocycle_zero hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
  · refine ⟨hh hU α hα f, ?_⟩
    rw [one_smul]
    funext i t
    refine (ev_d hU (hh hU α hα f) i (t ⋙ (capT U i).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
    rfl
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPull
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem prod_mem_fil {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) :
    ∀ (n : ℕ) (g : Fin n → Φ.A.obj T), (∀ k, g k ∈ Φ.J.S T) → ∏ k, g k ∈ (Fil n).S T
  | 0, g, _ => by
    have h := hF.top 0 le_rfl T
    simp only [Nat.cast_zero, h]
    exact Submodule.mem_top
  | n + 1, g, h => by
    rw [Fin.prod_univ_castSucc]
    have h1 : g (Fin.last n) ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
      rw [Nat.cast_one, hF.one]; exact h _
    exact hF.mul n 1 T (prod_mem_fil hF T n _ fun k => h _) h1

variable {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (σ : ∀ T : C, E.D ⟶ T)

theorem tau_sec_Pmap (i : Fin d) {T T' : C} (φ : T ⟶ T') :
    E.τ i.succ (Cut.sec Q ⟨T, σ T⟩ ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ) (Cut.sec Q ⟨T', σ T'⟩) =
      (Φ.A.map (Q.j T')).hom (E.τ i.succ (σ T ≫ φ) (σ T')) := by
  rw [Cut.τ_sec, if_neg (Fin.succ_ne_zero i), neg_zero, zero_add]
  have e : σ T ≫ Q.j T ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ = (σ T ≫ φ) ≫ Q.j T' := by
    have := Cut.Pmap_j Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ
    simp only at this
    rw [this, Category.assoc]
  simp only
  rw [e, E.add i.succ _ (σ T' ≫ Q.j T') _, E.nat]
  have h := Cut.sec_spec Q (E := E) ⟨T', σ T'⟩ i.succ
  simp only at h
  rw [h, if_neg (Fin.succ_ne_zero i), add_zero]

theorem factor {T₀ T₁ T₂ : C} (i : Fin d) (b : T₀ ⟶ T₁) (a : T₁ ⟶ T₂) :
    (Φ.A.map (Cut.Pmap Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a)).hom
      (E.τ i.succ (Cut.sec Q ⟨T₀, σ T₀⟩ ≫ Cut.Pmap Q (X := ⟨T₀, σ T₀⟩) (Y := ⟨T₁, σ T₁⟩) b) (Cut.sec Q ⟨T₁, σ T₁⟩)) =
      (Φ.A.map (Q.j T₂)).hom ((Φ.A.map a).hom (E.τ i.succ (σ T₀ ≫ b) (σ T₁))) := by
  rw [tau_sec_Pmap, ← Cut.mapA_comp, ← Cut.mapA_comp]
  have := Cut.Pmap_j Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a
  simp only at this
  rw [this]

variable {Fil : ℤ → IdF Φ.A}

theorem form_sub_mem (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) -
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) ∈
        (Fil (r + 1)).S (Q.P (s.obj (Fin.last j))) := by
  have e1 : ∀ k : Fin j, ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
      ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom ((Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
        (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))) :=
    fun k => factor Q σ (I k) _ _
  let P₀ : Φ.A.obj (s.obj (Fin.last j)) := ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))
  have hP : P₀ ∈ (Fil j).S (s.obj (Fin.last j)) :=
    prod_mem_fil hF _ j _ fun k => Φ.J.map_mem _ (E.mem _ _ _)
  let u : E.D ⟶ Q.P (s.obj (Fin.last j)) := Cut.sec Q ⟨s.obj (Fin.last j), σ _⟩
  let v : E.D ⟶ Q.P (s.obj (Fin.last j)) := σ (s.obj (Fin.last j)) ≫ Q.j _
  have f1 : (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map u).hom x := by
    have h : (∏ k : Fin j, (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from
        ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
          ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))))) =
        (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ :=
      (Finset.prod_congr rfl fun k _ => e1 k).trans (map_prod (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom _ _).symm
    exact congrArg (· * (Φ.A.map u).hom x) h
  have f2 : (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map v).hom x := by
    change (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (P₀ * (Φ.A.map (σ _)).hom x) = _
    rw [map_mul, ← Cut.mapA_comp]
  rw [f1, f2, ← mul_sub]
  have hcast : r + 1 = ((j + (q + 1) : ℕ) : ℤ) := by rw [hr]; push_cast; ring
  rw [hcast]
  refine hF.mul j (q + 1) _ ((Fil j).map_mem _ hP) ?_
  have := hc q u v hx
  have e : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [e]
  exact this

theorem gr_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s))
    (hg : ∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) :
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  funext s
  refine Subtype.ext ?_
  have h1 := hf (s ⋙ Cut.Pσ Q σ)
  have h2 := hg s
  change (show sqM _ _ _ from f (s ⋙ Cut.Pσ Q σ)).1 =
    Ideal.quotientMapₐ _ (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (fun _ hx => (Fil (r + 1)).map_mem _ hx)
      (show sqM _ _ _ from g s).1
  rw [h1, h2]
  exact Ideal.Quotient.eq.2 (form_sub_mem Q σ hF hc j q r hr I x hx s)

end
end GlobalTheory.CompanionTheory.GrPull
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.filtration_critical_comparison_map : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {d : ℕ} (E : Frame Φ (d + 1))
    (a b : ℤ → IdF Φ.A) (r : ℤ), (∀ r' T, (b r').S T ≤ (a r').S T) → Q.Crit a r → Q.Crit a (r - 1) → Q.Crit b r → Q.Crit b (r - 1) →
    ∃ β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)),
      (∀ X, Function.Injective ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom) ∧
      (∀ X, Function.Exact ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom (β.app X).hom) ∧
      (∀ X, Function.Surjective (β.app X).hom) ∧
      ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z' := by
  first | exact @GlobalTheory.CompanionTheory.PolySes.ses | exact GlobalTheory.CompanionTheory.PolySes.ses | (intros; apply GlobalTheory.CompanionTheory.PolySes.ses <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.bounded_cokernel_limit_to_level : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim → ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  first | exact @GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | exact GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | (intros; apply GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.perfect_tensor_generated_lift : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K](S₁ : Type) [CommRing S₁] (i : S →ₐ[A] B) (I : Ideal S) (κ : K →+* S₁) (j : S →+* S₁) (i₁ : S₁ →+* B ⊗[A] K), Pf p A → Pf p K → PQ p (i : S →+* B) I → κ.comp (algebraMap A K) = j.comp (algebraMap A S) → Subring.closure (Set.range κ ∪ Set.range j) = ⊤ → (∀ a, i₁ (κ a) = (1 : B) ⊗ₜ[A] a) → (∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K)) → PQ p i₁ (I.map j) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange | exact GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.etale_lifting_of_nil_ideal : ∀ {B : Type} [CommRing B] (J : Ideal B), (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  first | exact @GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | exact GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | (intros; apply GlobalTheory.CompanionTheory.EtNil.etLift_of_nil <;> assumption)
end
