module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.Bruhat

variable {F : Type} [Field F] {n : ℕ}

theorem perm_eq_of_le (τ : Equiv.Perm (Fin n)) (h : ∀ b, τ b ≤ b) (b : Fin n) : τ b = b := by
  have hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ))
    (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

def mono (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0

theorem mul_mono (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (A * mono m) a c = A a (m.1 c) * m.2 c := by
  simp [mono, Matrix.mul_apply]

theorem mono_mul (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (mono m * A) a c = m.2 (m.1.symm a) * A (m.1.symm a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]
  · simp [mono]
  · intro k _ hk
    have : a ≠ m.1 k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [mono, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_unique {m m' : Equiv.Perm (Fin n) × (Fin n → Fˣ)} {u u' : GL (Fin n) F} (hu : u ∈ unip F n)
    (hu' : u' ∈ unip F n)
    (h : (u : Matrix (Fin n) (Fin n) F) * mono m = mono m' * (u' : Matrix (Fin n) (Fin n) F)) : m = m' := by
  have key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) *
      (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b := by
    intro b
    have h1 := congrFun (congrFun h (m.1 b)) b
    rwa [mul_mono, mono_mul, unip_diag hu, one_mul] at h1
  have hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < m'.1.symm (m.1 b) := not_le.1 hlt
    apply (m.2 b).ne_zero
    rw [key b, unip_lower hu' hlt', mul_zero]
  have hfix : ∀ b, m'.1.symm (m.1 b) = b := fun b => perm_eq_of_le _ hle b
  refine Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)
  · have := congrArg m'.1 (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  · rw [key b, hfix b, unip_diag hu', mul_one]

theorem mem_unip_of {A : Matrix (Fin n) (Fin n) F} (hl : ∀ i j, j < i → A i j = 0) (hd : ∀ i, A i i = 1) :
    ∃ u ∈ unip F n, (u : Matrix (Fin n) (Fin n) F) = A := by
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]
    simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩

theorem exists_col_reduced (g : GL (Fin n) F) :
    ∃ u ∈ unip F n, ∃ σ : Equiv.Perm (Fin n),
      (∀ c, ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (σ c) c ≠ 0) ∧
      ∀ a c, σ c < a → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0 := by
  classical
  let P : ℕ → Prop := fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧
    ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0
  have hex : ∃ N, P N := ⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl,
    fun a c h => absurd a.2 (not_lt.2 h)⟩
  obtain ⟨u, hu, f, hf, hz⟩ := Nat.find_spec hex
  have hpos : ∀ c, 0 < f c := by
    intro c
    by_contra h0
    have h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      rw [hz k c (by omega), mul_zero]
  have hmin : ∀ v ∈ unip F n,
      (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) →
      ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0 := by
    intro v hv hzv c
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex := by
      rw [← hf]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · by_cases hk : k = c
        · subst hk; simp
        · rw [Function.update_of_ne hk]
      · have := hpos c
        rw [Function.update_self]; omega
    refine Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩
    by_cases hkc : k = c
    · subst hkc
      rw [Function.update_self] at hk
      by_cases h2 : f k ≤ a.val
      · exact hzv a k h2
      · exact hcon a (by omega)
    · rw [Function.update_of_ne hkc] at hk
      exact hzv a k hk
  choose s hs hsne using hmin u hu hz
  have hinj : ∀ k c, k < c → s k ≠ s c := by
    intro k c hkc he
    have hfe : f k = f c := by rw [← hs k, ← hs c, he]
    set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
    obtain ⟨t, ht, htv⟩ := mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k)))
      (fun i j hij => by
        have h1 : ¬ (k = i ∧ c = j) := by
          rintro ⟨rfl, rfl⟩; exact absurd hkc (not_lt.2 hij.le)
        simp [Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])
      (fun i => by
        have h1 : ¬ (k = i ∧ c = i) := by
          rintro ⟨rfl, h⟩; exact absurd h (ne_of_gt hkc)
        simp [Matrix.transvection, Matrix.single_apply, h1])
    have hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        H * Matrix.transvection k c (-(H (s c) c / H (s c) k)) := by
      rw [← mul_assoc, Units.val_mul, htv]
    obtain ⟨a, ha, hane⟩ := hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by
      rw [hval]
      by_cases hjc : j = c
      · subst hjc
        rw [Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]
        simp
      · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]
        exact hz a j hj) c
    have hac : a = s c := Fin.ext (by have := hs c; omega)
    apply hane
    have hk0 : H (s c) k ≠ 0 := he ▸ hsne k
    rw [hval, Matrix.mul_transvection_apply_same, hac]
    field_simp
    ring
  have hinj' : Function.Injective s := by
    intro k c he
    rcases lt_trichotomy k c with h | h | h
    · exact absurd he (hinj k c h)
    · exact h
    · exact absurd he.symm (hinj c k h)
  refine ⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩
  have h1 : (s c).val < a.val := h
  have := hs c
  omega

theorem exists_decomp (g : GL (Fin n) F) : ∃ m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n,
    (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * mono m * (u' : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨v, hv, σ, hne, hz⟩ := exists_col_reduced g
  set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
  obtain ⟨u, hu, huv⟩ := mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b))
    (fun i j hij => by
      rw [Matrix.of_apply, hz i _ (by simpa using hij), zero_div])
    (fun i => by
      have := hne (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [Matrix.of_apply, div_self this])
  refine ⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  have h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H := by
    ext a c
    rw [mul_mono, huv]
    simp [div_mul_cancel₀ _ (hne c)]
  rw [h1, hH, ← Units.val_mul, mul_inv_cancel_right]

theorem bruhat : ∀ (F : Type) [Field F] (n : ℕ) (g : GL (Fin n) F), ∃! m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n, (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * (Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0) * (u' : Matrix (Fin n) (Fin n) F) := by
  intro F _ n g
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  refine ⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩
  rintro m' ⟨v, hv, v', hv', h'⟩
  have h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u' := h'.symm.trans h
  refine mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_
  have h3 := congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X *
    ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact h3

end GlobalTheory.FinGL.Bruhat
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def vec {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (cc : Fin n → S) : Sp (DualNumber S) ⟶ t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst t.G.hom x

section V

variable {t} {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem push_ext {Y : Over (Spec (CommRingCat.of S))} {v v' : Y ⟶ (Over.pullback x).obj t.G}
    (h : v.left ≫ pullback.fst t.G.hom x = v'.left ≫ pullback.fst t.G.hom x) : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w v).trans (Over.w v').symm

theorem tan_iff (v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v.left ≫ pullback.fst t.G.hom x = (1 : Over.mk x ⟶ t.G).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have hid : (sp (R₀ := S) S).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e0 : (1 : sp (R₀ := S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x =
      (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))
  have e1 : (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _
    rw [hid, Category.id_comp]
  rw [← e1, ← e0, ← Category.assoc]
  constructor
  · intro e
    exact push_ext e
  · intro e
    exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem vec_tan (hx : IsUnivChart _ n xc) (cc : Fin n → S) : IsTanAtG t x (vec t x xc cc) := by
  refine ⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩
  show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))

theorem vec_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber S) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cc, w = vec t x xc cc := by
  let v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G :=
    Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)
  have hv : v.left ≫ pullback.fst t.G.hom x = w := pullback.lift_fst _ _ _
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := (tan_iff v).mp (by rw [hv]; exact hw.2)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩
  have e : v = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht
  rw [← hv]
  exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → S) (e : Fin m → Fin n → S) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0
    rw [add_zero] at h
    simpa using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]

theorem comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → S) (a : Fin m → S) (cc : Fin n → S) :
    IsCombAtG t x (fun j => vec t x xc (e j)) a (vec t x xc cc) ↔ cc = ∑ j, a j • e j := by
  let P := pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))
  let W' : Fin m → (tEpsG x ⟶ t.G) := fun j =>
    P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
  have hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j) := fun j =>
    Category.assoc _ _ _
  have hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j) := by
    have h := map_list_prod P
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
    rw [← tvec_sum hx a e, List.map_ofFn] at h
    exact (congrArg (fun q => q.left) h).symm
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)
    rw [eu', hP] at hprod
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm
  · intro h
    subst h
    exact ⟨W', hW', hP⟩

theorem vec_bc [IsLocalRing S] {S' : Type} [CommRing S'] [Algebra S S'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap S S') ≫ x)).obj t.G), IsUnivChart _ n xc' ∧
      ∀ cc : Fin n → S, vec t (spMap (algebraMap S S') ≫ x) xc' (algebraMap S S' ∘ cc) =
        spMap (dualMap (algebraMap S S')) ≫ vec t x xc cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

end V

theorem exists_lie_basis_stable (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X) :
    ∃ (n : ℕ) (D : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ e, IsTanAtG t x (D e)) ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (w : Sp (DualNumber S') ⟶ t.G.left),
        IsTanAtG t (spMap φ ≫ x) w →
          ∃! a : Fin n → S', IsCombAtG t (spMap φ ≫ x) (fun e => spMap (dualMap φ) ≫ D e) a w := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)
  refine ⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := S') hx
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  have hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) =
      fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1) := by
    funext e
    have h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S) := by
      funext j
      by_cases h : j = e
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact (hv _).symm.trans (by rw [← h1])
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm

end GlobalTheory.LieLocBasis
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.glBlock_finiteDim_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  first | exact @GlobalTheory.BlockReps.finite_module_structure | exact GlobalTheory.BlockReps.finite_module_structure | (intros; apply GlobalTheory.BlockReps.finite_module_structure <;> assumption)
end

section

noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.AdeleTensorModule

theorem adele_mod (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 1 ≤ N)
    (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ a : 𝓞 F, ∃ w ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) + (N : FiniteAdeleRing (𝓞 F) F) * w := by
  have hN0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (R := 𝓞 F) (K := F) y hy (N : 𝓞 F) hN0
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((N : F)⁻¹) *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀]
    have hv : Valued.v (algebraMap F (v.adicCompletion F) (N : F)) = v.intValuation (N : 𝓞 F) := by
      have := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R (K := F) v (N : 𝓞 F)
      rwa [map_natCast (algebraMap (𝓞 F) F)] at this
    have h0 : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
    rw [hv]
    calc (v.intValuation (N : 𝓞 F))⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
        ≤ (v.intValuation (N : 𝓞 F))⁻¹ * v.intValuation (N : 𝓞 F) := by
          gcongr
          exact ha v
      _ = 1 := inv_mul_cancel₀ h0
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hNF, map_one, one_mul]
    ring

theorem tens_mod (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 1 ≤ N) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∃ a ∈ Formalism.UG.intOE E,
      ∃ z ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F),
        x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a +
          (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z := by
  set S := Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) with hS
  set ι := Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hl : ∀ a ∈ Formalism.UG.intOE E, ι a ∈ S := fun a ha =>
    Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)
  have hr : ∀ w ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] w ∈ S := fun w hw =>
    Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨a, a.2, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨a, w, hw, e⟩ := adele_mod F N hN y y.2
      refine ⟨algebraMap F E (a : F), ⟨algebraMap (𝓞 F) (𝓞 E) a, rfl⟩, (1 : E) ⊗ₜ[F] w, hr w hw, ?_⟩
      have e2 := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := E)
        (B := FiniteAdeleRing (𝓞 F) F)) e
      rw [map_add (f := _), map_mul, map_natCast, AlgHom.commutes] at e2
      exact e2
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by rw [map_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by rw [map_one, mul_zero, add_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    exact ⟨a + b, add_mem ha hb, z + w, add_mem hz hw, by rw [map_add (f := _)]; ring⟩
  | neg x _ ihx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    exact ⟨-a, neg_mem ha, -z, neg_mem hz, by rw [map_neg]; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    refine ⟨a * b, mul_mem ha hb, ι a * w + z * ι b + (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (z * w),
      add_mem (add_mem (mul_mem (hl a ha) hw) (mul_mem hz (hl b hb)))
        (mul_mem (natCast_mem S N) (mul_mem hz hw)), ?_⟩
    rw [map_mul]; ring

theorem main : ∀ {D : Formalism.BasicNotions.D7} (N : ℕ), (1 : ℕ) ≤ N → ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    ∃ a ∈ Formalism.UG.intOE ((Formalism.BasicNotions.D7.host D).E), ∃ z ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
      x = (Formalism.MainNotions.StandardLatticesGL3.inc D : (Formalism.BasicNotions.D7.host D).E → Formalism.MainNotions.StandardLatticesGL3.AE D) a +
        (↑N : Formalism.MainNotions.StandardLatticesGL3.AE D) * z :=
  fun {D} N hN x hx => tens_mod ℚ D.host.E N hN x hx

end GlobalTheory.AdeleTensorModule

end
end
