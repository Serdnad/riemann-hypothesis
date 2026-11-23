module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle002
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle021
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOnPrimeStratum
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace UpperTheory.Lev

variable {G : GDatum}

def MN (n : ℕ) (a b : G.La) : Prop := ∃ c : G.La, a = b + n • c

structure IsLSim (n : ℕ) (f : G.La → G.La) (ν : ℤ) : Prop where
  add : ∀ x y, MN n (f (x + y)) (f x + f y)
  lin : ∀ (c : G.O) x, MN n (f (c • x)) (c • f x)
  inj : ∀ x, MN n (f x) 0 → MN n x 0
  surj : ∀ y, ∃ x, MN n (f x) y
  cop : IsCoprime ν (n : ℤ)
  isom : ∀ x y, (n : ℤ) ∣ 2 * G.EF (f x) (f y) - ν * (2 * G.EF x y)

structure GSim (G : GDatum) where
  f : ℕ → G.La → G.La
  ν : ℕ → ℤ
  sim : ∀ n, 0 < n → IsLSim n (f n) (ν n)
  tower : ∀ n m : ℕ, 0 < n → 0 < m → ∀ x, MN n (f (n * m) x) (f n x)
  νtower : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n

variable {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

end UpperTheory.Lev
end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem UpperTheory.power_zero_isIso {S : Scheme.{0}} (A : Over S) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let g : Over.mk (𝟙 S) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let f : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 S) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have hfg : f ≫ g = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨g.left, ?_, ?_⟩⟩
  · have h := congrArg (fun x => x.left) hfg
    simpa [f] using h
  · simpa using Over.w g

private theorem UpperTheory.power_succ_lift {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (a : T ⟶ GlobalTheory.KS.pow A m) (b : T ⟶ A) :
    ∃ l : T ⟶ GlobalTheory.KS.pow A (m + 1),
      l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) = a ∧
      l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) = b := by
  refine ⟨Pi.lift fun j => Fin.lastCases (motive := fun _ => T ⟶ A) b
    (fun i => a ≫ Pi.π (fun _ : Fin m => A) i) j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    simp
  · simp

private theorem UpperTheory.power_succ_lift_unique {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (l l' : T ⟶ GlobalTheory.KS.pow A (m + 1))
    (h₁ : l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) =
      l' ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc))
    (h₂ : l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) =
      l' ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)) : l = l' := by
  refine Pi.hom_ext _ _ fun j => ?_
  induction j using Fin.lastCases with
  | last => exact h₂
  | cast i => simpa using congrArg (· ≫ Pi.π (fun _ : Fin m => A) i) h₁

theorem UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback :
    ∀ {S : Scheme.{0}} (A : Over S), IsIso (GlobalTheory.KS.pow A 0).hom ∧ ∀ m : ℕ, ∃ (u : (GlobalTheory.KS.pow A (m + 1)).left ⟶ (GlobalTheory.KS.pow A m).left) (v : (GlobalTheory.KS.pow A (m + 1)).left ⟶ A.left), IsPullback u v (GlobalTheory.KS.pow A m).hom A.hom ∧ u ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A (m + 1)).hom := by
  intro S A
  refine ⟨UpperTheory.power_zero_isIso A, fun m => ?_⟩
  let P : GlobalTheory.KS.pow A (m + 1) ⟶ GlobalTheory.KS.pow A m :=
    Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc
  let Q : GlobalTheory.KS.pow A (m + 1) ⟶ A := Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)
  have w : P.left ≫ (GlobalTheory.KS.pow A m).hom = Q.left ≫ A.hom := (Over.w P).trans (Over.w Q).symm
  have hL := fun s : PullbackCone (GlobalTheory.KS.pow A m).hom A.hom =>
    UpperTheory.power_succ_lift A m (Over.mk (s.snd ≫ A.hom)) (Over.homMk s.fst s.condition)
      (Over.homMk s.snd rfl)
  refine ⟨P.left, Q.left, IsPullback.of_isLimit' ⟨w⟩
    (PullbackCone.IsLimit.mk w (fun s => (hL s).choose.left) ?_ ?_ ?_), Over.w P⟩
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.1]
    rfl
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.2]
    rfl
  · intro s n hn1 hn2
    have hn : n ≫ (GlobalTheory.KS.pow A (m + 1)).hom = s.snd ≫ A.hom := by
      rw [← Over.w Q, ← Category.assoc, hn2]
    let N : Over.mk (s.snd ≫ A.hom) ⟶ GlobalTheory.KS.pow A (m + 1) := Over.homMk n hn
    have h1 : N ≫ P = (hL s).choose ≫ P := by
      rw [(hL s).choose_spec.1]
      apply (Over.forget S).map_injective
      simpa [N] using hn1
    have h2 : N ≫ Q = (hL s).choose ≫ Q := by
      rw [(hL s).choose_spec.2]
      apply (Over.forget S).map_injective
      simpa [N] using hn2
    exact congrArg (fun x => x.left) (UpperTheory.power_succ_lift_unique A m _ N _ h1 h2)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology :
    ∀ (F : Shv ℤ) (P : PSh) (n : ℤ), Subsingleton (H ℤ (disc.obj P) F n) → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n) := by
  intro F P n hs
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf ℤ
  haveI : (res ℤ F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).1
  haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
  have hb := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso ℤ (e P).hom (res ℤ F) n
  exact hb.2.subsingleton
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

noncomputable section

private def cut (C : DC) (x : C.Tot) : C.Tot
  | 0, s => x 0 s
  | _ + 1, _ => 0

private theorem unit_map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (u : ℤˣ) (a : A) :
    f (u • a) = u • f a := by
  simp [Units.smul_def]

private theorem split (C : DC) (rd : ∀ p s, C.A (p + 1) s →+ C.A p s)
    (h0 : ∀ p s, Even p → ∀ a, C.δ p s a = 0)
    (h1 : ∀ p s, Odd p → ∀ a, C.δ p s (rd p s a) = a)
    (h2 : ∀ p s, Odd p → ∀ a, rd p s (C.δ p s a) = a)
    (h3 : ∀ p s t a, C.d p s t (rd p s a) = rd p t (C.d (p + 1) s t a))
    (m : ℤ) (x : C.Tot) (hd : C.Deg m x) (hD : C.D m x = 0) :
    C.Deg m (cut C x) ∧ C.D m (cut C x) = 0 ∧ C.Deg m (x - cut C x) ∧
      ∃ y, C.Deg (m - 1) y ∧ C.D (m - 1) y = x - cut C x := by
  have key : ∀ (q : ℕ) (s : ℤ) (a : C.A q s), m.negOnePow • m.negOnePow • a = a := by
    intro q s a
    rw [smul_smul, Int.units_mul_self, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p s hps
    cases p with
    | zero => exact hd 0 s hps
    | succ p => rfl
  · funext p t
    cases p with
    | zero =>
      have := congrFun (congrFun hD 0) t
      simpa [DC.D, cut] using this
    | succ p =>
      cases p with
      | zero => simp [DC.D, cut, h0 0 t ⟨0, rfl⟩]
      | succ p => simp [DC.D, cut]
  · intro p s hps
    cases p with
    | zero => simp [cut]
    | succ p => simp [cut, hd (p + 1) s hps]
  · refine ⟨fun p t => if Odd p then m.negOnePow • rd p t (x (p + 1) t) else 0, ?_, ?_⟩
    · intro p t hpt
      dsimp only
      split_ifs
      · rw [hd (p + 1) t (by push_cast; omega)]
        simp
      · rfl
    · funext p t
      cases p with
      | zero => simp [DC.D, cut]
      | succ p =>
        have hx := congrFun (congrFun hD (p + 2)) t
        simp only [DC.D] at hx
        simp only [DC.D, cut, sub_add_cancel, Pi.sub_apply, sub_zero]
        rcases Nat.even_or_odd p with hp | hp
        · have hp1 : Odd (p + 1) := hp.add_one
          have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
          simp only [hp1, hp0, if_true, if_false, map_zero, smul_zero, add_zero]
          rw [unit_map, h3]
          have hx' : C.d (p + 2) (t - 1) t (x (p + 2) (t - 1)) = m.negOnePow • C.δ (p + 1) t (x (p + 1) t) := by
            rw [Int.negOnePow_succ] at hx
            rw [eq_neg_of_add_eq_zero_left hx, Units.neg_smul, neg_neg]
          rw [hx', unit_map, h2 _ _ hp1, key]
        · have hp1 : ¬ Odd (p + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr hp
          simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
          rw [unit_map, h1 _ _ hp, key]

private theorem alt {G : Type*} [AddCommGroup G] (b : G) (n : ℕ) :
    ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) • b = if Even n then 0 else b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', h.neg_one_pow]
    · have h' : Even (n + 1) := by simpa [Nat.even_add_one] using h
      have ho : Odd n := Nat.not_even_iff_odd.1 h
      simp [h, h', ho.neg_one_pow]

section Concrete
variable {R : Type} [CommRing R] {X : Scheme.{0}}

private def rdF (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (p : ℕ) (M : Shv R) : Fam Z (p + 1) M →+ Fam Z p M where
  toFun a := ⟨fun W t => a.1 W t, fun V W g t => a.2.1 V W g t, fun W t h => a.2.2 W t (hZ _ _ _ _ h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem delta_apply (Z : Sub (sch.obj X)) (p : ℕ) (M : Shv R) (a : Fam Z p M) (W : Scheme.{0}) (t : W ⟶ X) :
    (Fam.δ Z p M (0 : ℤ).negOnePow a).1 W t = if Even (p + 2) then 0 else a.1 W t := by
  change (0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W t = _
  rw [Int.negOnePow_zero, one_smul, alt]

private theorem fam_split (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (K : Cx R) (m : ℤ) (x : (famDC Z K 0).Tot) (hd : (famDC Z K 0).Deg m x) (hD : (famDC Z K 0).D m x = 0) :
    (famDC Z K 0).Deg m (cut _ x) ∧ (famDC Z K 0).D m (cut _ x) = 0 ∧ (famDC Z K 0).Deg m (x - cut _ x) ∧
      ∃ y, (famDC Z K 0).Deg (m - 1) y ∧ (famDC Z K 0).D (m - 1) y = x - cut _ x := by
  refine split (famDC Z K 0) (fun p s => rdF Z hZ p (K.X (s + 0))) ?_ ?_ ?_ ?_ m x hd hD
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : Even (p + 2) := by rw [Nat.even_add]; simp [hp]
    rw [if_pos this] at e
    exact e
  · intro p s hp (a : Fam Z (p + 1) (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) (rdF Z hZ p (K.X (s + 0)) a) W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s t a
    rfl

end Concrete

theorem UpperTheory.exists_section_representing_relativeClass :
    ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (m j : ℤ) (c : Hs q (opn U) m j), ∃ β : Sec ((res _ (tw q j)).X m) X, IsRep U β c.1 := by
  intro q X U m j c
  have TM := UpperTheory.relativeCohomology_isTotalModel_of_image q (opn U) j 0 m m (by simp)
  have hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X),
      (Sub.img (opn U).hom).mem p W t → (Sub.img (opn U).hom).mem q W t :=
    fun _ _ _ _ h => h
  obtain ⟨x, hxd, hxD, hxr⟩ := TM.surj c
  obtain ⟨hcd, hcD, hrd, y, hyd, hyD⟩ := fam_split (Sub.img (opn U).hom) hZ _ m x hxd hxD
  obtain ⟨c0, hc0⟩ := TM.ex _ hcd hcD
  have hsub := TM.sub _ _ _ _ hxr hc0
  have hz : c - c0 = 0 := (TM.zero _ _ hrd hsub).2 ⟨y, hyd, hyD⟩
  have hcc : c = c0 := sub_eq_zero.mp hz
  rw [← hcc] at hc0
  obtain ⟨γ, hγ, hcomp, hinr⟩ := hc0
  have cover := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) (opn U)).1
  have hhi : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + m = s) (W : Scheme)
      (z : Sx (dbl (opn U)) (p + 1) W), ev γ.1 (p + 1) s h W z = 0 := by
    intro p s h W z
    rcases cover (p + 1) W z with ⟨z', rfl⟩ | ⟨z', rfl⟩
    · have e : ∀ h' : -((p + 1 : ℕ) : ℤ) + m = s + 0,
          ev γ.1 (p + 1) (s + 0) h' W (Sx.map (dbl.inl (opn U)) z') = 0 := by
        intro h'
        rw [← hcomp (p + 1) s h' W z']
        rfl
      rw [add_zero] at e
      exact e h
    · exact hinr (p + 1) s h W z'
  have big : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 0),
      (∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)))) ∧
      Sec.res U.ι (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have nat : ∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) := by
      intro W t
      have e1 := hcomp 0 m h W t
      have e2 := hcomp 0 m h X (show Sx (opn U).right 0 X from 𝟙 X)
      have e := (cut _ x 0 m).2.1 W X t (show Sx (opn U).right 0 X from 𝟙 X)
      have r : Sx.res t (show Sx (opn U).right 0 X from 𝟙 X) = (show Sx (opn U).right 0 W from t) :=
        Category.comp_id t
      exact e1.symm.trans ((congrArg (fun z => (cut _ x 0 m).1 W z) r.symm).trans
        (e.symm.trans (congrArg (Sec.res t) e2)))
    refine ⟨nat, ?_⟩
    rw [← nat]
    have mem : (Sub.img (opn U).hom).mem 0 U U.ι := by
      refine ⟨(show Sx (sch.obj (U : Scheme.{0})) 0 U from 𝟙 (U : Scheme.{0})), ?_⟩
      dsimp [Sx.map, opn, sch, disc]
      simp
    exact (hcomp 0 m h U U.ι).symm.trans ((cut _ x 0 m).2.2 U U.ι mem)
  rw [add_zero] at big
  have dz : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 1 - 1 + 0),
      Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))
        (ev γ.1 0 (m + 1 - 1 + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have e2 := hcomp 0 (m + 1 - 1) h X (show Sx (opn U).right 0 X from 𝟙 X)
    have e := congrArg (fun a => a.1 X (show Sx (opn U).right 0 X from 𝟙 X)) (congrFun (congrFun hcD 0) (m + 1))
    refine (congrArg (Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))) e2).symm.trans ?_
    exact e
  rw [add_zero, add_zero, add_sub_cancel_right] at dz
  exact ⟨ev γ.1 0 m (by simp) X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)),
    dz _, (big _).2, γ, hγ, fun W t => (big _).1 W t, fun W t => hinr 0 m _ W t, hhi⟩

end
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.finite_kummerSelmer_of_charts :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], Charts k K q → FinCls q (SelAll k K q) := by
  intro k K _ _ _ _ _ q _ hC
  obtain ⟨n, v, hv⟩ := UpperTheory.exists_finite_span_kummerSelmer_representatives k K q
  let P : Set (Fin n → k) → Prop := fun s =>
    FinCls q {f | f ∈ SelAll k K q ∧ ∃ c, (f : K) = ∑ i, c i • v i ∧ c ∈ s}
  have hall : P Set.univ := by
    apply UpperTheory.Et.noethSp k n P
    · refine ⟨∅, ?_⟩
      rintro f ⟨_, c, _, hc⟩
      exact absurd hc (by simp)
    · intro s t hst ⟨T, hT⟩
      refine ⟨T, ?_⟩
      rintro f ⟨hf, c, hfc, hc⟩
      exact hT f ⟨hf, c, hfc, hst hc⟩
    · intro s t ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
      classical
      refine ⟨T₁ ∪ T₂, ?_⟩
      rintro f ⟨hf, c, hfc, hc | hc⟩
      · obtain ⟨x, hx, u, hu⟩ := h₁ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_left _ hx, u, hu⟩
      · obtain ⟨x, hx, u, hu⟩ := h₂ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_right _ hx, u, hu⟩
    · intro I hI
      obtain ⟨g, hg, T, hT⟩ := UpperTheory.finite_kummerSelmer_on_prime_stratum k K q hC n v I hI
      refine ⟨g, hg, T, ?_⟩
      rintro f ⟨hf, c, hfc, hc₁, hc₂⟩
      exact hT f ⟨hf, c, hfc, hc₁, hc₂⟩
  obtain ⟨T, hT⟩ := hall
  refine ⟨T, ?_⟩
  intro f hf
  obtain ⟨g, hg, ⟨c, hgc⟩, u, hfu⟩ := hv f hf
  obtain ⟨t, ht, w, hw⟩ := hT g ⟨hg, c, hgc, Set.mem_univ c⟩
  refine ⟨t, ht, w * u, ?_⟩
  rw [hfu, hw, mul_pow, mul_assoc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) [IsEmpty T] (a : Sec F T) : a = 0 :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩

private theorem free_sec_zero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) (U : Scheme.{0})
    (y : Sec ((free R).obj P) U) : y = 0 := by
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨c, hc⟩ := h V g hg
  have h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0 := map_zero (((free R).obj P).obj.map g.op).hom
  rw [h0]
  by_cases hV : IsEmpty V
  · exact sec_empty _ _ _
  · rw [hc]
    have : IsEmpty (P.obj (op V)) := ⟨fun x => hV (hP V ⟨x⟩)⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    simp [hc0]

private theorem free_isZero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) : IsZero ((free R).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U y
  exact free_sec_zero R P hP U.unop y

private theorem sx_empty (E : Spc) (p : ℕ) (T : Scheme.{0})
    (x : Sx (pullback (triv E 0) (PGL.pr 0)) p T) : IsEmpty T := by
  have y : Sx (PGL 0) p T := Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x
  have v : Um 0 Γ(T, ⊤) := (show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0
  have h : (⊥ : Ideal Γ(T, ⊤)) = ⊤ := by
    have := v.2
    rwa [Set.range_eq_empty, Ideal.span_empty] at this
  have hs : Subsingleton Γ(T, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn
    · exact hs
    · exact absurd h bot_ne_top
  refine ⟨fun t => ?_⟩
  have := (T.presheaf.germ ⊤ t trivial).hom.codomain_trivial
  exact not_subsingleton (T.presheaf.stalk t) this

private theorem chains_isZero (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (k : ℤ) :
    IsZero (((chains R).obj X).X k) := by
  by_cases hk : k ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact (free_isZero R _ (hX p)).of_iso (chainsXIso R X p)
  · refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_
    change -(i : ℤ) ≠ k
    omega

private theorem H_subsingleton (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (F : Shv R) (n : ℤ) :
    Subsingleton (H R X F n) := ⟨fun a b => by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  congr 1
  exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩

theorem UpperTheory.projectiveBundleFormula_rank_zero :
    ∀ (q : ℕ) [NeZero q] (E : Spc), PBF q E 0 := by
  intro q _ E n i
  haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) :=
    H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩
end
