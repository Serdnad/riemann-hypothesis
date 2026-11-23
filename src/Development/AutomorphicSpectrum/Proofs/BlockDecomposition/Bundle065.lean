module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032

@[expose] public section

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.reduction_unique_up_to_parabolic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | exact GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | (intros; apply GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

theorem chain_ext {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : ∀ i, c.obj i = c'.obj i) : c = c' :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

theorem chain_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {i j : Fin (n + 1)} (h : i ≤ j) :
    (c.obj j).unop ≤ (c.obj i).unop :=
  leOfHom (c.map (homOfLE h)).unop

def snocObj {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) : Fin (n + 2) → Pᵒᵖ :=
  Fin.snoc (α := fun _ ↦ Pᵒᵖ) (fun i ↦ c.obj i) (op b)

@[simp] theorem snocObj_last {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) :
    snocObj c b (Fin.last _) = op b :=
  Fin.snoc_last (α := fun _ ↦ Pᵒᵖ) _ _

@[simp] theorem snocObj_castSucc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (i : Fin (n + 1)) :
    snocObj c b i.castSucc = c.obj i :=
  Fin.snoc_castSucc (α := fun _ ↦ Pᵒᵖ) _ _ _

theorem snocObj_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P} (hb : b ≤ (c.obj (Fin.last n)).unop)
    {i j : Fin (n + 2)} (h : i ≤ j) : (snocObj c b j).unop ≤ (snocObj c b i).unop := by
  induction j using Fin.lastCases with
  | last =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
    induction i using Fin.lastCases with
    | last => exact le_of_eq (by rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last])
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last i))
  | cast j =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    induction i using Fin.lastCases with
    | last => exact absurd h (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.castSucc_le_castSucc_iff.mp h)

def snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    Fin (n + 2) ⥤ Pᵒᵖ where
  obj := snocObj c b
  map h := (homOfLE (snocObj_anti c hb (leOfHom h))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem snoc_last_le {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    b ≤ ((snoc c b hb).obj (Fin.last _)).unop :=
  le_of_eq (congrArg Opposite.unop (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last c b)).symm

abbrev face {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) : Fin (n + 1) ⥤ Pᵒᵖ :=
  (Fin.succAboveOrderEmb i).toOrderHom.monotone.functor ⋙ c

theorem face_le {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : b ≤ ((face i c).obj (Fin.last _)).unop :=
  hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last _))

theorem face_castSucc_snoc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) :
    face i.castSucc (snoc c b hb) = snoc (face i c) b (face_le i c hb) := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  induction k using Fin.lastCases with
  | last =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.last _)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.last _)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)),
      Fin.succ_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
  | cast k =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.castSucc k)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.castSucc k)
    rw [Fin.castSucc_succAbove_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    all_goals rfl

theorem face_last_snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : face (Fin.last _) (snoc c b hb) = c := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.last _).succAbove k) = c.obj k
  rw [Fin.succAbove_last_apply, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]

def valL (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) : NC (coind M) n →ₗ[R] M b where
  toFun f := f c ⟨b, hb⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valL_congr (M : P → ModuleCat.{0} R) {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : c = c') (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) (hb' : b ≤ (c'.obj (Fin.last n)).unop) (f : NC (coind M) n) :
    valL M c b hb f = valL M c' b hb' f := by
  subst h
  rfl

theorem valL_dNC (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 2) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last _)).unop) (f : NC (coind M) n) :
    valL M c b hb (dNC (coind M) n f) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • valL M (face i c) b (face_le i c hb) f := by
  first
    | (simp only [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul];
        all_goals exact Finset.sum_congr rfl fun i _ => rfl)
    | (rw [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, map_sum];
        exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, map_smul]; rfl)

def contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) : NC (coind M) n :=
  fun c b ↦ valL M (snoc c b.1 b.2) b.1 (snoc_last_le c b.1 b.2) f

theorem valL_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) :
    valL M c b hb (contr M f) = valL M (snoc c b hb) b (snoc_last_le c b hb) f := rfl

theorem NC_ext (M : P → ModuleCat.{0} R) {n : ℕ} {f g : NC (coind M) n}
    (h : ∀ c b hb, valL M c b hb f = valL M c b hb g) : f = g := by
  funext c b
  exact h c b.1 b.2

theorem dNC_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1))
    (hf : dNC (coind M) (n + 1) f = 0) :
    dNC (coind M) n (((-1 : R) ^ (n + 1)) • contr M f) = f := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.NC_ext
  intro c b hb
  have hcoc : GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc c b hb) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc_last_le c b hb)
      (GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) f) = 0 := by
    rw [hf, map_zero]
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, Fin.sum_univ_castSucc] at hcoc
  have hsum : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_le i c hb)
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M f) =
      -((-1 : R) ^ (n + 1 + 1) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M c b hb f) := by
    rw [eq_neg_iff_add_eq_zero, ← hcoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_contr]
      exact congrArg ((-1 : R) ^ (i : ℕ) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_castSucc_snoc i c hb).symm b _ _ f)
    · rw [Fin.val_last]
      exact congrArg ((-1 : R) ^ (n + 1 + 1) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_last_snoc c hb).symm b _ _ f)
  have hp : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [map_smul, map_smul, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, hsum, smul_neg, smul_smul,
    pow_succ (-1 : R) (n + 1), ← mul_assoc, hp, one_mul, neg_smul, one_smul, neg_neg]

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc


open GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc in
theorem GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (M : P → ModuleCat.{0} R) (n : ℕ) : IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) x = 0 := by
    change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d (n + 1) (n + 1 + 1)).hom x = 0 at hx
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d] at hx
    exact hx
  refine ⟨((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x, ?_⟩
  change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d n (n + 1)).hom
    (((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x) = x
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]
  exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.dNC_contr M x hx'
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type}

abbrev BV (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) : Type :=
  ∀ _ : PLift (∀ j ∈ s, b ≤ e j), M b

def bRes (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s t : Finset κ} (h : s ⊆ t) :
    BV e M b s →ₗ[R] BV e M b t where
  toFun x ht := x ⟨fun j hj ↦ ht.down j (h hj)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cubeB (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (BV e M b s)) (fun h ↦ bRes e M b h) (fun _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl)

theorem cubeB_bijective [DecidableEq κ] (e : κ → P) (M : P → ModuleCat.{0} R) {b : P} {i : κ} (hi : e i = b)
    (s : Finset κ) (_his : i ∉ s) :
    Function.Bijective (Cube.res (cubeB e M b) (Finset.subset_insert i s)) := by
  have key : ∀ hs : PLift (∀ j ∈ s, b ≤ e j), ∀ j ∈ insert i s, b ≤ e j := fun hs j hj ↦ by
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hi.ge
    · exact hs.down j hj
  constructor
  · intro x y h
    exact funext fun hs ↦ congrFun h ⟨key hs⟩
  · intro y
    exact ⟨fun hs ↦ (show BV e M b (insert i s) from y) ⟨key hs⟩, rfl⟩

abbrev AV (e : κ → P) (M : P → ModuleCat.{0} R) (s : Finset κ) : Type :=
  ∀ hs : PLift s.Nonempty, ∀ b : {b : P // b ≤ s.inf' hs.down e}, M b.1

def prj (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) :
    (cubeOf e (coind M)).obj s →ₗ[R] (cubeB e M b).obj s where
  toFun x := fun h ↦ if hs : s.Nonempty then
    (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ else 0
  map_add' x y := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; exact (add_zero _).symm
  map_smul' r x := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; show (0 : M b) = r • (0 : M b); exact (smul_zero r).symm

theorem prj_apply (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) (h : PLift (∀ j ∈ s, b ≤ e j)) :
    (show BV e M b s from prj e M b s x) h =
      (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ :=
  dif_pos hs

theorem prj_empty (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : ¬ s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) : prj e M b s x = 0 :=
  funext fun _ ↦ dif_neg hs

def prjHom (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : cubeOf e (coind M) ⟶ cubeB e M b :=
  Cube.homMk κ R (prj e M b) fun {s t} h x ↦ by
    by_cases hs : s.Nonempty
    · refine funext fun ht ↦ ?_
      have hs' : t.Nonempty := hs.mono h
      refine (prj_apply e M b hs' _ ht).trans ?_
      refine Eq.trans ?_ (prj_apply e M b hs x ⟨fun j hj ↦ ht.down j (h hj)⟩).symm
      have := cubeRes_apply e (coind M) h x hs ⟨hs'⟩
      exact congrFun this _
    · rw [prj_empty e M b hs, map_zero]
      by_cases ht : t.Nonempty
      · refine funext fun hh ↦ ?_
        refine (prj_apply e M b ht _ hh).trans ?_
        have := cubeRes_empty e (coind M) h x hs ⟨ht⟩
        exact congrFun this _
      · exact prj_empty e M b ht _

theorem term_ext (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (u v : Cube.Term (cubeOf e (coind M)) (q + 1))
    (h : ∀ b, Cube.termMap (prjHom e M b) (q + 1) u = Cube.termMap (prjHom e M b) (q + 1) v) :
    u = v := by
  funext s
  refine funext fun hs ↦ funext fun b ↦ ?_
  have hle : ∀ j ∈ s.1, b.1 ≤ e j := fun j hj ↦ b.2.trans (Finset.inf'_le e hj)
  have h1 := congrFun (congrFun (h b.1) s) ⟨hle⟩
  exact (prj_apply e M b.1 hs.down (u s) ⟨hle⟩).symm.trans (h1.trans (prj_apply e M b.1 hs.down (v s) ⟨hle⟩))

def asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ} (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) :
    Cube.Term (cubeOf e (coind M)) (q + 1) :=
  fun s ↦ (show AV e M s.1 from fun _ b ↦
    (show BV e M b.1 s.1 from y b.1 s) ⟨fun _ hj ↦ b.2.trans (Finset.inf'_le e hj)⟩)

theorem termMap_asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) (b : P) :
    Cube.termMap (prjHom e M b) (q + 1) (asm e M y) = y b := by
  funext s
  refine funext fun h ↦ ?_
  have hs : s.1.Nonempty := Finset.card_pos.1 (by have := s.2; omega)
  exact prj_apply e M b hs (asm e M y s) h

variable [LinearOrder κ]

theorem exact_d (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (p : ℕ) :
    Function.Exact (Cube.d (cubeOf e (coind M)) (p + 1)) (Cube.d (cubeOf e (coind M)) (p + 2)) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ _ y⟩
  have hb : ∀ b, ∃ y : Cube.Term (cubeB e M b) (p + 1),
      Cube.d (cubeB e M b) (p + 1) y = Cube.termMap (prjHom e M b) (p + 2) x := by
    intro b
    obtain ⟨i, hi⟩ := he b
    refine (Cube.exact_d_of_bijective (cubeB e M b) i (cubeB_bijective e M hi) (p + 1) _).1 ?_
    rw [← Cube.termMap_d, hx, map_zero]
  choose y hy using hb
  refine ⟨asm e M y, term_ext e M _ _ fun b ↦ ?_⟩
  rw [Cube.termMap_d, termMap_asm, hy]

theorem isZero_homology (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (n : ℕ) :
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff (cubeOf e (coind M)) n).2 (exact_d e he M n))

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.HaarUnimod

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem modularCharacterFun_eq_one (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g

theorem isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]

end GlobalTheory.CompanionTheory.HaarUnimod
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.unramified_quotient_card : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | exact GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_quot_lev <;> assumption)
end
