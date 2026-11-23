module

public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle022
public import Development.EtaleCohomology.TateTwists.Bundle024
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib

namespace LateralTheory.EtaleFoundations.EtaDelta
variable {R : Type} [CommRing R]

theorem along_face {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E M U)
    (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk M) (i : Fin (p + 2)) :
    (x.along a).face i = x.along (SimplexCategory.δ i ≫ a) :=
  along_comp x a (SimplexCategory.δ i)

theorem face_along {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E (M + 1) U) (i : Fin (M + 2))
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk M) :
    (x.face i).along a = x.along (a ≫ SimplexCategory.δ i) :=
  along_comp x (SimplexCategory.δ i) a

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem phi_eq {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) :
    phi μ hk α β x w c = Finsupp.linearCombination ℤ (phiT μ hk α β x w) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem phiT_face {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (i : Fin (M + 2)) (w : ℤ) (z : Pr M) :
    phiT μ hk α β (x.face i) w z =
      phiT μ hk α β x w ⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ i, z.2.2.2 ≫ SimplexCategory.δ i⟩ := by
  simp only [phiT, face_along]

theorem phi_bd {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (w : ℤ) (c : Pr M →₀ ℤ) :
    ∑ i : Fin (M + 2), (-1 : ℤ) ^ (i : ℕ) • phi μ hk α β (x.face i) w c = phi μ hk α β x w (Pr.bd c) := by

  simp only [phi_eq, Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply,
  Finsupp.linearCombination_mapDomain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact congrArg _ (funext fun z => phiT_face μ hk α β x i w z)

theorem phiT_Fm {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phiT μ hk α β x w ⟨p, r, a, b⟩ = ((m * (p : ℤ)).negOnePow : ℤ) • Fm μ α β U w p r (x.along a) (x.along b) := by
  dsimp only [phiT, Fm]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rw [smul_zero]

end

theorem ev_zero' {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have := ev_sub' (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rwa [sub_self, sub_self] at this

theorem d_ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (hst : s + 1 = t) (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s t) (ev α.1 p s hs U y) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α.1 q t hh U z else 0) p y := by
  have h := ev_delta_bd (n := n) (m := n + 1) rfl α.1 p s t hs (by omega) U y
  rw [Cocycle.δ_eq_zero, ev_zero', Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul] at h
  exact add_neg_eq_zero.mp h.symm

theorem bd_zero' {E : Spc} {U : Scheme.{0}} {G : Type*} [AddCommGroup G] (p : ℕ) (y : Sx E p U) :
    bd (E := E) (U := U) (fun _ _ => (0 : G)) p y = 0 := by
  cases p <;> simp [bd]

theorem mul_zsmul_left {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h (c • a) b = c • μ.mul U s t w h a b := by
  rw [map_zsmul]; rfl

theorem mul_zsmul_right {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h a (c • b) = c • μ.mul U s t w h a b :=
  map_zsmul _ c b

theorem d_Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cocycle ((chains R).obj E) I n)
    (β : Cocycle ((chains R).obj E) J m) (U : Scheme.{0}) (s t : ℤ) (hst : s + 1 = t) (p r : ℕ)
    (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d s t) (Fm μ α.1 β.1 U s p r y z) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q y' => Fm μ α.1 β.1 U t q r y' z) p y +
      ((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) • bd (fun q z' => Fm μ α.1 β.1 U t p q y z') r z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = s
  · have e : Fm μ α.1 β.1 U s p r y z = μ.mul U _ _ s h (ev α.1 p _ rfl U y) (ev β.1 r _ rfl U z) := by
      unfold Fm; rw [dite_eq_left h]
    rw [e, leib' μ U _ _ s (-(p : ℤ) + n + 1) (-(r : ℤ) + m + 1) t h rfl rfl hst,
      d_ev α p _ _ rfl rfl, d_ev β r _ _ rfl rfl, mul_zsmul_left, mul_zsmul_right, mul_bd_left, mul_bd_right,
      Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    · refine bd_congr (fun q y' hq => ?_) y
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · refine bd_congr (fun q z' hq => ?_) z
      unfold Fm
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have e : Fm μ α.1 β.1 U s p r y z = 0 := by unfold Fm; rw [dite_eq_right h]
    have h0 := secmap_zsmul (K.d s t) (0 : ℤ) (0 : Sec (K.X s) U)
    rw [zero_smul, zero_smul] at h0
    rw [e, h0]
    rw [bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q y' hq => by unfold Fm; rw [dite_eq_right (by omega)]) y,
      bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q z' hq => by unfold Fm; rw [dite_eq_right (by omega)]) z,
      bd_zero', bd_zero', smul_zero, smul_zero, add_zero]

theorem secmap_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add ((φ.hom.app (op U)).hom) a b

theorem secmap_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero ((φ.hom.app (op U)).hom)

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)

theorem part1 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((n.negOnePow : ℤˣ) : ℤ) •
      bd (fun q y' => Fm μ α.1 β.1 U t q r y' (x.along b)) p (x.along a)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t) (Pr.d₁ (⟨p, r, a, b⟩ : Pr N)) := by
  cases p with
  | zero => simp [bd, Pr.d₁]
  | succ p =>
    show _ = _ • Finsupp.linearCombination ℤ _
      (∑ i : Fin (p + 2), Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) ((-1 : ℤ) ^ (i : ℕ)))

    simp only [bd, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by push_cast; ring⟩

theorem part2 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) •
      bd (fun q z' => Fm μ α.1 β.1 U t p q (x.along a) z') r (x.along b)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
      ((-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N)) := by
  cases r with
  | zero => simp [bd, Pr.d₂]
  | succ r =>
    show _ = _ • Finsupp.linearCombination ℤ _ ((-1 : ℤ) ^ p •
      ∑ j : Fin (r + 2), Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) ((-1 : ℤ) ^ (j : ℕ)))

    simp only [bd, map_zsmul, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum,
    smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p : ℤ), by push_cast; ring⟩

theorem d_phiT {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (z : Pr N) :
    Sec.map (K.d s t) (phiT μ hk α.1 β.1 x s z) =
      ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
        (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [phiT_Fm, secmap_zsmul, d_Fm μ α β U s t hst, smul_add, map_add (f := _), smul_add, part1 μ hk α β, part2 μ hk α β]

theorem d_phi {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (c : Pr N →₀ ℤ) :
    Sec.map (K.d s t) (phi μ hk α.1 β.1 x s c) = ((k.negOnePow : ℤˣ) : ℤ) • phi μ hk α.1 β.1 x t (Pr.d N c) := by
  rw [phi_eq, phi_eq]
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [map_zero, secmap_zero', smul_zero]
  · intro f g hf hg
    rw [map_add (f := _), map_add (f := _), map_add (f := _), secmap_add', hf, hg, smul_add]
  · intro z a
    rw [Finsupp.linearCombination_single, secmap_zsmul, d_phiT μ hk α β x s t hst]
    unfold Pr.d
    rw [Finsupp.linearCombination_single, map_zsmul, smul_comm]

theorem phi_add {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c + d) = phi μ hk α.1 β.1 x w c + phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_add (f := _)]

theorem phi_sub {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c - d) = phi μ hk α.1 β.1 x w c - phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_sub]

end

end LateralTheory.EtaleFoundations.EtaDelta


open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.EtaDelta in
theorem LateralTheory.EtaleFoundations.cupflip_eta_delta_of : LateralTheory.EtaleFoundations.cupflip_eta_delta := by
  intro h hs R _ I J K μ E n m k hk α β η hη N t ht U x
  cases N with
  | zero =>
    rw [ev_delta_zero (n := k - 1) (by omega) η (-((0 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη 0 _ _ U x,
      d_phi μ hk α β x _ t (by omega), hs.2.1, phi_sub]
  | succ M =>
    rw [ev_delta_succ (n := k - 1) (by omega) η M (-((M + 1 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη (M + 1) _ _ U x]
    simp only [hη]
    rw [Units.smul_def, phi_bd, d_phi μ hk α β x _ t (by omega), ← smul_add, ← phi_add, hs.2.2 M, phi_sub]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awex_sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact ((E.map (SimplexCategory.subinterval j l h).op).naturality_apply g.op x)

theorem awex_freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)) (ModuleCat.freeMk (ULift.up x))
  refine e.symm.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem awex_ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  unfold ev Sec.res
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)) (freeGen R _ U x)
  refine e.symm.trans ?_
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom y)
    (awex_freeGen_res (R := R) _ g x)

theorem awex_lift_single {S : Type*} [Semiring S] {X M : Type*} [AddCommMonoid M] [Module S M]
    (f : X → M) (x : X) : Finsupp.lift M S X f (Finsupp.single x 1) = f x := by
  simp

noncomputable def awexNat {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.ofHom (Finsupp.lift _ (ULift.{1} R) _
        (fun y : ULift.{1} (Sx E p (unop U)) => a p s h (unop U) y.down))
  naturality := by
        intro U V g
        refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_)
        have e := ModuleCat.free_map_apply (R := ULift.{1} R)
          (uliftFunctor.{1}.map ((E.obj (op (SimplexCategory.mk p))).map g)) y
        change (Finsupp.lift _ (ULift.{1} R) _ _) (((freeP R).obj _).map g |>.hom (Finsupp.single y 1)) =
          ((I.X s).obj.map g).hom ((Finsupp.lift _ (ULift.{1} R) _ _) (Finsupp.single y 1))
        erw [e]
        refine (awex_lift_single (S := ULift.{1} R) _ _).trans ?_
        refine Eq.trans ?_ (congrArg ((I.X s).obj.map g).hom (awex_lift_single (S := ULift.{1} R) _ _).symm)
        exact (ha p s h (unop V) (unop U) g.unop y.down).symm

noncomputable def awexPhi {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ (I.X s)).symm (awexNat a ha p s h)

theorem awexPhi_freeGen {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((awexPhi a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology (awexNat a ha p s h) (I.X s).property
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (congrArg (fun φ => φ.app (op U)) e))
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))
  refine e2.trans ?_
  exact awex_lift_single (S := ULift.{1} R) (fun y : ULift.{1} (Sx E p U) => a p s h U y.down) (ULift.up x)

def EtaleSimplicialCochainFromNaturalEvaluationsExists : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

theorem etale_alexander_whitney_cup_exists_of_cochain_from_evaluations (hmk : EtaleSimplicialCochainFromNaturalEvaluationsExists) : EtaleAlexanderWhitneyCupCochainExistsForPairing := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hmk R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x

      simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [awex_sub_res, awex_sub_res, ← awex_ev_res, ← awex_ev_res]
      exact μ.nat g _ _ _ _ _ _)
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

noncomputable def awexCochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun x y hxy => if hx : x ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show x = -(((-x).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-x).toNat).hom ≫ awexPhi a ha (-x).toNat y (by omega)
  else 0

theorem awex_key {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (q p : ℕ) (e : q = p) (he : -(p : ℤ) = -(q : ℤ)) (s : ℤ) (h : -(p : ℤ) + n = s) (hq : -(q : ℤ) + n = s) :
    (chainsXIso R E p).inv ≫ (((chains R).obj E).XIsoOfEq he).hom ≫ (chainsXIso R E q).hom ≫ awexPhi a ha q s hq =
      awexPhi a ha p s h := by
  subst e
  simp

theorem awex_ev {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (awexCochain a ha) p s h U x = a p s h U x := by
  unfold ev
  rw [awexCochain, Cochain.mk_v, dite_eq_left (by omega), awex_key a ha _ p (by omega)]
  exact awexPhi_freeGen a ha p s h U x

theorem etale_simplicial_cochain_from_natural_evaluations_exists_holds : EtaleSimplicialCochainFromNaturalEvaluationsExists := by
  intro R _ E I n a ha
  exact ⟨awexCochain a ha, awex_ev a ha⟩

theorem etale_alexander_whitney_cup_cochain_exists_holds : EtaleAlexanderWhitneyCupCochainExistsForPairing :=
  etale_alexander_whitney_cup_exists_of_cochain_from_evaluations etale_simplicial_cochain_from_natural_evaluations_exists_holds

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

theorem stair_tens_top {R : Type} [CommRing R] {C J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens C J U w) :
    ∃ s : ℤ, ∀ p, s < p.1.1 → x p = 0 := by
  classical
  refine ⟨((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ), fun p hp => ?_⟩
  by_contra h
  have hm : p ∈ DFinsupp.support x := (DFinsupp.mem_support_iff).2 h
  have h1 : p.1.1.toNat ≤ (DFinsupp.support x).sup fun p => p.1.1.toNat := Finset.le_sup (f := fun p => p.1.1.toNat) hm
  have h2 : p.1.1 ≤ (p.1.1.toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((p.1.1.toNat : ℕ) : ℤ) ≤ (((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ) : ℤ) := by exact_mod_cast h1
  omega

theorem stair_loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem stair_sec_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) (U : Scheme.{0}) (y : Sec F U) : y = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have := congrArg (fun m : F ⟶ F => (m.hom.app (op U)).hom y) h
  simpa using this

theorem stair_tens_low {R : Type} [CommRing R] {C J : Cx R} (a : ℤ) [C.IsStrictlyGE a] {U : Scheme.{0}} {w : ℤ}
    (x : Tens C J U w) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (hp : p.1.1 < a) : x p = 0 := by
  have hz := C.isZero_of_isStrictlyGE a p.1.1 hp
  have key : ∀ y : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U, y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul u v => rw [stair_sec_zero hz U u, TensorProduct.zero_tmul]
    | add u v hu hv => rw [hu, hv, add_zero]
  exact key _

theorem stair_fg_zero {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.sc w).X₁ V) :
    Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = 0 := by
  have h1 : Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = ((((T.sc w).f ≫ (T.sc w).g).hom.app (op V)).hom z) := rfl
  rw [h1, (T.sc w).zero]
  rfl

def stair_row (R : Type) [CommRing R] (C J : Cx R) : Prop :=
  ∀ (s t : ℤ) (V : Scheme.{0}) (x : Sec (C.X s) V ⊗[ULift.{1} R] Sec (J.X t) V),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x = 0 →
    Loc V fun W k => ∃ z : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] Sec (J.X t) W,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id z =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom x

def EtaleTensorWithFlatPreservesLocalExactness : Prop :=
  ∀ (R : Type) [CommRing R] {C J : Cx R}, (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    stair_row R C J

def EtaleTensorCycleLocallyLowersTopDegree : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → stair_row R C J →
    ∀ (w s : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, s < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ x' : Tens C J V w, (∀ p, s - 1 < p.1.1 → x' p = 0) ∧
        ∃ z : Sec (T.sc w).X₁ V, τ.lift V w x' = Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)

theorem etale_tensor_cycles_locally_lift_of_row_exact_and_descent (hA : EtaleTensorWithFlatPreservesLocalExactness)
    (hS : EtaleTensorCycleLocallyLowersTopDegree) : EtaleTensorCyclesLocallyLiftOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC
  have hrow := hA R hJ hC
  have key : ∀ n : ℕ, ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, a - 1 + n < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x) := by
    intro n
    induction n with
    | zero =>
      intro w U x hx _
      have h0 : x = 0 := by
        ext p
        by_cases hp : p.1.1 < a
        · simpa using stair_tens_low a x p hp
        · simpa using hx p (by push_cast; omega)
      refine stair_loc_top _ _ fun V g => ⟨0, ?_⟩
      simp [h0] <;> rfl
    | succ n ih =>
      intro w U x hx hc
      refine stair_loc_bind U _ _ (hS R τ hτ hrow w (a - 1 + (n + 1 : ℕ)) U x hx hc) ?_
      rintro V g ⟨x', hx', z, hz⟩
      have hc' : Sec.map (T.sc w).g (τ.lift V w x') = 0 := by
        rw [hz]
        have e1 : Sec.map (T.sc w).g (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
            Sec.map (T.sc w).g (Sec.res g (τ.lift U w x)) - Sec.map (T.sc w).g (Sec.map (T.sc w).f z) := by
          exact map_sub _ _ _
        rw [e1, stair_fg_zero, sub_zero]
        exact (stair_map_res (T.sc w).g g (τ.lift U w x)).trans ((congrArg (Sec.res g) hc).trans (map_zero _))
      refine stair_loc_mono V _ _ (ih w V x' (fun p hp => hx' p (by push_cast at hp ⊢; omega)) hc') ?_
      rintro W k ⟨z', hz'⟩
      refine ⟨z' + Sec.res k z, ?_⟩
      have e2 : Sec.map (T.sc w).f (z' + Sec.res k z) = Sec.map (T.sc w).f z' + Sec.map (T.sc w).f (Sec.res k z) := by
        simp only [Sec.map, map_add (f := _)]
      have e3 : Sec.res k (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
          Sec.res k (Sec.res g (τ.lift U w x)) - Sec.res k (show Sec (T.X w) V from Sec.map (T.sc w).f z) := by
        exact map_sub _ _ _
      rw [e2, hz', hz, e3, stair_map_res, stair_res_res]
      exact sub_add_cancel _ _
  intro w U x hx
  obtain ⟨s, hs⟩ := stair_tens_top x
  exact key (s - (a - 1)).toNat w U x (fun p hp => hs p (by omega)) hx

end LateralTheory.EtaleFoundations
end
