module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.formVanish_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  intro Rg _ A₀ T X N mA mB a φ p t c d F hF z q q' hq hq'
  have hV : φ z ∈ N.U q ⊓ N.U q' := ⟨hq, hq'⟩
  have hsec : ∀ i, gs φ z (N.U q) ((a i).f q) =
      (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * gs φ z (N.U q') ((a i).f q') := by
    intro i
    rw [← gs_res φ z (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q) hV, (a i).compat q q', gs_mul φ z _ hV,
      gs_unit φ z _ hV, gs_res φ z (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q') hV]
  have hcomb : comb a φ p c z q = fun j => (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    funext j
    simp only [comb, hsec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hev : ∀ (w : X.presheaf.stalk z) (y : Fin mB → X.presheaf.stalk z),
      MvPolynomial.eval₂Hom (gc (p ≫ t) z) (fun j => w * y j) F = w ^ d * MvPolynomial.eval₂Hom (gc (p ≫ t) z) y F := by
    intro w y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hd := hF (MvPolynomial.mem_support_iff.mp hm)
    have hs : ∑ i ∈ m.support, m i = d := by
      rw [← hd]; simp [Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring
  rw [hcomb, hev]
  exact IsUnit.mul_right_eq_zero ((gm φ z (N.U q ⊓ N.U q') (N.g q q')).isUnit.pow d)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv.CondGen

theorem gs_appLE_self {X Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (z : Y)
    (hz : z ∈ W) (f : Γ(X, U)) : gs (𝟙 Y) z W ((q.appLE U W e).hom f) = gs q z U f := by
  have h1 := gs_res (𝟙 Y) z e hz ((q.app U).hom f)
  have h2 := gs_pull (𝟙 Y) q z U (e hz) f
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

end GlobalTheory.HomFixUniv.CondGen


open GlobalTheory.HomFixUniv.CondGen in
theorem GlobalTheory.HomFixUniv.isGen_of_matRel : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  intro Rg _ A B _ _ L M k mA mB bA bB R _ A' B' Φ' ψA ψB c u hG hR p p'
  apply unit_ext
  intro z hz
  have hzp : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := hz.1
  have hzp' : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p' := hz.2
  have hmB : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hzp.1
  have hmB' : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p'.1 hzp'.1
  have hmA : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hzp.2
  have hmA' : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p'.2 hzp'.2
  have key : ∀ (q : (Fin 1 → M.ι) × (Fin 1 → L.ι)), z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U q → ∀ j : Fin mB,
      gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) q.1) ((bB j).f q.1) =
        (gm (𝟙 _) z _ (u q)).val * GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z q.2 j := by
    intro q hq j
    have e := congrArg (gs (𝟙 A'.left) z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U q)) (hR j q)
    refine (gs_appLE_self _ _ _ _ z hq _).symm.trans (e.trans ?_)
    rw [gs_mul _ z _ hq, gs_unit _ z _ hq, gs_fsum _ z _ hq]
    unfold GlobalTheory.HomFixUniv.comb
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ z _ hq]
    exact congrArg₂ (· * ·) (gs_appLE_self _ _ _ _ z hq _) (gs_appLE_self _ _ _ _ z hq _)
  have tB : ∀ j : Fin mB, gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) =
      (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val *
        gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1) ((bB j).f p'.1) :=
    fun j => sec_trans (bB j) (Φ'.left ≫ ψB) z hmB hmB'
  have tA : ∀ i : Fin mA, gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) ((bA i).f p.2) =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2) ((bA i).f p'.2) :=
    fun i => sec_trans (bA i) ψA z hmA hmA'
  have tC : ∀ j : Fin mB, GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p.2 j =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j := by
    intro j
    unfold GlobalTheory.HomFixUniv.comb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrArg (_ * ·) (tA i)).trans (mul_left_comm _ _ _)
  have hg : gm (𝟙 A'.left) z _ ((isoLB (L := L) (M := M) k Φ' ψA ψB).g p p') =
      trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1 *
        (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹ := by
    show gm (𝟙 A'.left) z _ (res _ _ * (res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ?_)
      ((map_inv _ _).trans (congrArg _ ((gm_res _ z _ hz _).trans ?_))))
    · exact (gm_linComb M _ _ (𝟙 A'.left) z p.1 p'.1 hzp.1 hzp'.1).trans (by simp only [trF, Category.id_comp])
    · exact (gm_linComb L _ _ (𝟙 A'.left) z p.2 p'.2 hzp.2 hzp'.2).trans (by simp only [trF, Category.id_comp])
  obtain ⟨j, hj⟩ := hG z p.2 hmA
  refine (gm_res _ z _ hz _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  rw [hg, gm_res _ z _ hz]
  apply Units.ext
  apply hj.mul_right_cancel
  have e1 := key p hzp j
  have e2 := key p' hzp' j
  have e3 := tB j
  have e4 := tC j
  have hinv := Units.inv_mul (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)
  rw [e1, e2, e4] at e3
  simp only [Units.val_mul]
  rw [e4]
  set TM := (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val
  set TL := (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val
  set TLi := ((trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹).val
  set U' := (gm (𝟙 A'.left) z _ (u p')).val
  set C' := GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j
  linear_combination e3 - (TM * U' * C') * hinv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUnivVals

open TopologicalSpace Opposite

theorem comp_base_pt {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem glue_fn {X : Scheme.{0}} {J : Type} (W : J → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup W) (a : ∀ i, Γ(X, W i))
    (h : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 X) x (W i) (a i) = gs (𝟙 X) x (W j) (a j)) :
    ∃ α : Γ(X, ⊤), ∀ i x, x ∈ W i → gs (𝟙 X) x ⊤ α = gs (𝟙 X) x (W i) (a i) := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hc a
    (fun i j => fn_ext (V := W i ⊓ W j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((h i j y hy.1 hy.2).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun i x hx => ?_⟩
  exact (gs_res (𝟙 X) x (le_top : W i ≤ ⊤) hx s).symm.trans (congrArg (gs (𝟙 X) x (W i)) (hs i))

theorem vals (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))) (hL : L.IsLB) (hA : eA.IsGen) :
    ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  set S : Scheme.{0} := (𝟙_ (Over (Sp Rg))).left with hS
  set e : S ⟶ (topS Rg ⊗ A).left := eSec A ≫ θ A with he_def
  have he : e ≫ (snd (topS Rg) A).left = eSec A := by
    rw [he_def, Category.assoc, θ_snd, Category.comp_id]
  have memN : ∀ (z : S) (q : Fin 1 → L.ι), e z ∈ (LPow A L (k : ℤ) (topS Rg)).U q ↔ eSec A z ∈ L.U (q 0) := by
    intro z q
    constructor
    · intro h
      have h0 := Set.mem_iInter.1 h 0
      rw [Set.mem_preimage, ← comp_base_pt, he] at h0
      exact h0
    · intro h
      refine Set.mem_iInter.2 fun t => ?_
      rw [Subsingleton.elim t 0, Set.mem_preimage, ← comp_base_pt, he]
      exact h
  let W : L.ι → S.Opens := fun i => e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => i)
  have memW : ∀ (z : S) (i : L.ι), z ∈ W i ↔ eSec A z ∈ L.U i := by
    intro z i
    constructor
    · intro h; exact mem_pull.1 h.2
    · intro h; exact ⟨(memN z _).2 h, mem_pull.2 h⟩
  let a : ∀ i, Γ(S, W i) := fun i =>
    (S.presheaf.map (homOfLE (inf_le_left : W i ≤ e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i))).op).hom ((e.app _).hom (s.f (fun _ => i))) *
      ((res (inf_le_right : W i ≤ (L.pull (eSec A)).U (fun _ => i)) (eA.s (fun _ => i)))⁻¹ ^ k).val
  have ga : ∀ i x, x ∈ W i → gs (𝟙 S) x (W i) (a i) =
      gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i)) (s.f (fun _ => i)) * ((gm (𝟙 S) x _ (eA.s (fun _ => i)))⁻¹ ^ k).val := by
    intro i x hx
    rw [gs_mul (𝟙 S) x _ hx, gs_res (𝟙 S) x _ hx, gs_pull (𝟙 S) e x _ hx.1, Category.id_comp, gs_unit (𝟙 S) x _ hx,
      map_pow, map_inv, gm_res (𝟙 S) x _ hx]

  have compat : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 S) x (W i) (a i) = gs (𝟙 S) x (W j) (a j) := by
    intro i j x hx hy
    have hxi := (memW x i).1 hx
    have hxj := (memW x j).1 hy
    have hx' : e x ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j) := ⟨hx.1, hy.1⟩
    have mem : (snd (topS Rg) A).left (e x) ∈ L.U i ⊓ L.U j := by
      rw [← comp_base_pt, he]; exact ⟨hxi, hxj⟩
    have hg : gm e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) ((LPow A L (k : ℤ) (topS Rg)).g (fun _ => i) (fun _ => j)) =
        (gm (eSec A) x _ (L.g i j)) ^ k := by
      show gm e x _ (∏ _t : Fin 1, (res _ (pullU (snd (topS Rg) A).left _ (L.g i j))) ^ (k : ℤ)) = _
      rw [Fintype.prod_unique, map_zpow]
      erw [gm_res e x _ hx']
      rw [gm_pull e _ x _ mem, he, zpow_natCast]
    have hs := congrArg (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j))) (s.compat (fun _ => i) (fun _ => j))
    rw [gs_res e x _ hx', gs_mul e x _ hx', gs_res e x _ hx', gs_unit e x _ hx', hg] at hs
    have hp : x ∈ (L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j) := ⟨hx.2, hy.2⟩
    have mem' : (eSec A) ((𝟙 S : S ⟶ S) x) ∈ L.U i ⊓ L.U j := ⟨hxi, hxj⟩
    have hg' : gm (𝟙 S) x _ ((L.pull (eSec A)).g (fun _ => i) (fun _ => j)) = gm (eSec A) x _ (L.g i j) := by
      show gm (𝟙 S) x _ (∏ _t : PUnit, (res _ (pullU (eSec A) _ (L.g i j))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      erw [gm_res (𝟙 S) x _ hp]
      rw [gm_pull (𝟙 S) (eSec A) x _ mem', Category.id_comp]
    have hA' := congrArg (gm (𝟙 S) x ((L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j)))
      (hA (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ x _ hp, gm_res _ x _ hp, hg'] at hA'
    rw [ga i x hx, ga j x hy, hs, hA']
    set u := gm (eSec A) x _ (L.g i j)
    set B := gm (𝟙 S) x _ (eA.s (fun _ => j))
    have hinv : (u * B)⁻¹ ^ k = (u ^ k)⁻¹ * B⁻¹ ^ k := by rw [mul_inv, mul_pow, inv_pow]
    have hU : (u ^ k).val * ((u ^ k)⁻¹).val = 1 := Units.mul_inv _
    rw [hinv, Units.val_mul]
    linear_combination (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) (s.f (fun _ => j)) * (B⁻¹ ^ k).val) * hU
  obtain ⟨α, hα⟩ := glue_fn W (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (eSec A x)
      exact Opens.mem_iSup.2 ⟨i, (memW x i).2 hi⟩) a compat
  refine ⟨α, fun z q hz => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = fun _ => i := ⟨q 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
  have hzW : z ∈ W i := (memW z i).2 ((memN z _).1 hz)
  rw [hα i z hzW, ga i z hzW]
  show _ = _ * ((gm (𝟙 S) z _ (eA.s fun _ => i)) ^ k).val
  rw [_root_.mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.HomFixUnivVals
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_

  rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

end GlobalTheory.HomFixUniv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenericEnd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem eq_of_generic (U : UnifPre I D A G) {g g' : G ⟶ G}
    (h : (Over.pullback (jK R)).map g = (Over.pullback (jK R)).map g') : g = g' := by
  have := U.smooth
  have := U.separated
  have : IsSchemeTheoreticallyDominant (jK R) :=
    schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_
  have e := congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

theorem exists_generic_of_formal (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) (hb : FormalEnd U a h' b) (g : G ⟶ G) (hg : IsMonHom g)
    (hgb : ∀ e, (Over.pullback (thick R I e)).map g = b e) :
    ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g' : G ⟶ G, IsMonHom g' →
      (Over.pullback (jK R)).map g' ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U a h' g' := by
  have := U.gen_hom
  refine ⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩
  obtain rfl : g' = g := eq_of_generic U (by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f => f ≫ U.gen.inv) hg')
  intro e
  obtain ⟨t, ht, hi⟩ := hb.2.2.2 e
  exact ⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩

end GlobalTheory.Mum.GenericEnd
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R) (c : G.cocycles) (B : G.funs), G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 → c ∈ LinearMap.range G.cob := by
  first | exact @GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | exact GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP | (intros; apply GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP <;> assumption)
end
