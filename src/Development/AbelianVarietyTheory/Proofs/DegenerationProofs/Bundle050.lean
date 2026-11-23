module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem eq_zero_of_forall_pow_smul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : 1 < n) (v : X)
    (h : ∀ j : ℕ, ∃ z, v = n ^ j • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr v i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr v i).natAbs : ℕ) : ℤ)) ⟨b.repr z i, ?_⟩ ?_
  · have := congrArg (fun w => b.repr w i) hz
    simpa only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] using this
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hn

theorem exists_qt_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ p' : N'.QT k, p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2 := by
  have t := NumD.hom_transport O O (RingHom.id O) N N' (TateInh.homOfIso J)
  obtain ⟨g, r, hu⟩ := t.1 p.1.2
  have rp : ∀ m, (TateInh.homOfIso J).Rel (p.1.2 ^ m) (g ^ m) := by
    intro m
    induction m with
    | zero =>
      have h := t.2.2.1 0
      simpa [N.io_zero, N'.io_zero] using h
    | succ m ih => simpa [pow_succ] using t.2.1 _ _ _ _ ih r
  have r₂ := rp k
  rw [N.mem_QT.1 p.2] at r₂
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, r⟩
  exact (t.1 _).unique r₂ (t.2.2.1 _)

theorem iso_comm_of_labels : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' J hJ hs α α' gam ha ha' y
  have hk : ∀ j, 0 < n ^ j := fun j => pow_pos (by omega) j
  have key : ∀ j x, ∃ z, J.e (lab (n ^ j) x).1.1.toAdd = (lab' (n ^ j) x).1.1.toAdd + n ^ j • z := by
    intro j x
    obtain ⟨p', e, r⟩ := exists_qt_image J (lab (n ^ j) x)
    obtain ⟨x₀, h, h'⟩ := hJ j _ p' e r
    have h₁ := (hL'.2.1 _ (hk j) x₀ x).2 ((hL.2.1 _ (hk j) x₀ x).1 h)
    obtain ⟨z, hz, _⟩ := h₁
    obtain ⟨w, hw, _⟩ := h'
    refine ⟨w - z, ?_⟩
    rw [← e, hw, hz, smul_sub]
    abel
  refine sub_eq_zero.1 (eq_zero_of_forall_pow_smul hn _ fun j => ?_)
  obtain ⟨p, rfl⟩ := hs j y
  obtain ⟨x, z₀, h₀, -⟩ := hL.2.2.1 _ (hk j) p
  obtain ⟨z₁, h₁⟩ := ha j x
  obtain ⟨z₂, h₂⟩ := ha' j x
  obtain ⟨z₃, h₃⟩ := key j x
  obtain ⟨z₄, h₄⟩ := key j (gam x)
  refine ⟨J.e (α z₀) - J.e z₁ + z₄ + z₂ - α' z₃ - α' (J.e z₀), ?_⟩
  rw [h₁, h₂, map_add (f := _), map_nsmul] at h₄
  rw [h₀]
  simp only [map_add (f := _), map_nsmul, h₃]
  linear_combination (norm := module) h₄

end GlobalTheory.ModelData
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormSec
open scoped Pointwise

theorem map_form {B B' J : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') (T : Finset (J →₀ ℕ))
    (c : (J →₀ ℕ) → B) (s : J → B) :
    ψ (∑ m ∈ T, c m * m.prod (fun i n => s i ^ n)) =
      ∑ m ∈ T, ψ (c m) * m.prod (fun i n => ψ (s i) ^ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]

theorem form_scale {B J : Type} [CommRing B] (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → B) (u : B) (s : J → B) :
    ∑ m ∈ T, c m * m.prod (fun i n => (u * s i) ^ n) =
      u ^ d * ∑ m ∈ T, c m * m.prod (fun i n => s i ^ n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]
  ring

section Supp
variable {A X : Type} [CommRing A] [AddCommGroup X]

theorem supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)
  exact Set.add_mem_add (hx hb) (hy hc)

theorem supp_one : ((1 : AddMonoidAlgebra A X).coeff.support : Set X) ⊆ 0 := by
  intro a ha
  have := AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha
  simpa using this

theorem supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx

theorem supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]; exact supp_one
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]
    exact supp_mul (supp_pow (hx j) _) ih

theorem supp_form {B J : Type} [CommRing B] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → A) (s : J → B) (S : Set X)
    (hs : ∀ i α, ((Equiv.ofBijective _ hb).symm (s i)).coeff α ≠ 0 → α ∈ S) (α : X)
    (hα : ((Equiv.ofBijective _ hb).symm (∑ m ∈ T, f (c m) * m.prod (fun i n => s i ^ n))).coeff α ≠ 0) :
    ∃ β : Fin d → X, (∀ n, β n ∈ S) ∧ α = ∑ n, β n := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm.toRingHom _).coeff α ≠ 0 at hα
  rw [map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hα
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0 := by
    change ((e.symm (f (c m))).coeff.support : Set X) ⊆ 0
    rw [h1, AddMonoidAlgebra.coeff_single]
    intro a ha
    simpa using Finsupp.support_single_subset ha
  have h3 := supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S)
    (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)
  rw [zero_add, hT m hm, Set.mem_nsmul] at h3
  obtain ⟨β, hβ⟩ := h3
  exact ⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩

end Supp

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _ := by
    refine (Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_
    generalize_proofs h₁
    revert h₁
    rw [hx]
    intro h₁
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Category.id_comp _).trans ((Sp R).presheaf.map_id _)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a
  rw [e, Category.id_comp, Iso.inv_hom_id]
  rfl

theorem deg_of_mem {k J : Type} [Field k] {d : ℕ} {Pf : MvPolynomial J k} (h : Pf.IsHomogeneous d) :
    ∀ m ∈ Pf.support, ∑ i ∈ m.support, m i = d := fun m hm => by
  have := h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using this

def formSec {k : Type} [Field k] (Φ : FibPre k) {J : Type} (F : J → (Φ.H 1).Sec) {d : ℕ}
    (Pf : MvPolynomial J k) (h : Pf.IsHomogeneous d) : (Φ.H d).Sec where
  f l := ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) *
    m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)
  compat l l' := by
    let V : Φ.G.left.Opens := (Φ.H d).U l ⊓ (Φ.H d).U l'
    let r : Γ(Φ.G.left, (Φ.H d).U l) →+* Γ(Φ.G.left, V) := resG _ inf_le_left
    let r' : Γ(Φ.G.left, (Φ.H d).U l') →+* Γ(Φ.G.left, V) := resG _ inf_le_right
    let u : Γ(Φ.G.left, V)ˣ := pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l')
    have hF : ∀ i, r ((F i).f l) = (u : Γ(Φ.G.left, V)) * r' ((F i).f l') := fun i => by
      have := (F i).compat l l'
      change r ((F i).f l) = ((u ^ 1 : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' ((F i).f l') at this
      exact this.trans (congrArg (fun w : Γ(Φ.G.left, V)ˣ => (w : Γ(Φ.G.left, V)) * r' ((F i).f l')) (pow_one u))
    change r _ = ((u ^ d : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' _
    rw [map_form, map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [res_constFn, res_constFn]
    congr 2
    funext i n
    exact congrArg (· ^ n) (hF i)

theorem exists_formSec : (∀ (k : Type) [Field k] (Φ : FibPre k) (J : Type) (F : J → (Φ.H 1).Sec) (d : ℕ) (Pf : MvPolynomial J k), Pf.IsHomogeneous d → ∃ φ : (Φ.H d).Sec, (∀ l, φ.f l = ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) * m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)) ∧ (∀ α ∈ Φ.supp φ, ∃ β : Fin d → Φ.E.X, (∀ n, ∃ i, β n ∈ Φ.supp (F i)) ∧ α = ∑ n, β n) ∧ ∀ (x : Φ.Pt) (v : J → k), Crd (Φ.H 1) F x.left v → (MvPolynomial.eval v Pf = 0 ↔ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)) := by
  intro k _ Φ J F d Pf h
  refine ⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩
  · rintro α ⟨l, hl⟩
    refine supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h)
      (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)}
      (fun i β hβ => ⟨i, l, hβ⟩) α ?_
    simp only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]
    exact hl
  · rintro x v ⟨l, c, hl, hv⟩
    have hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l := hl
    have hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf) := by
      refine ⟨l, c ^ d, hl', fun _ => ?_⟩
      rw [CrdCalc.valR_eq _ _ hl']
      change _ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)
      rw [map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [valHom_constFn _ _ (Over.w x)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hv i, CrdCalc.valR_eq _ _ hl]
      rfl
    rw [← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]

end GlobalTheory.ZH.FormSec
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ImmSep
open GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem eq_of_valHom_eq (x x' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valHom x U h = valHom x' U h') : x = x' := by
  have e₁ : x.appLE U ⊤ h = x'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp R)) h
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec x' hU (isAffineOpen_top (Sp R)) h'
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem valHom_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    valHom x U h (constFn p U a) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (((x ≫ p).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  rw [← Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ le_top h]
  rfl

theorem eq_of_crd_eq : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x x' : Sp R ⟶ X) (v : J → R), x ≫ p = x' ≫ p → Crd H s x v → Crd H s x' v → x = x') := by
  intro k _ X p H J s J₀ _ hI R _ _ x x' v hp hx hx'
  have hm : x (IsLocalRing.closedPoint R) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by
    rw [hI.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨hi₀, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have h := (top_le_iff x _).2 hi
  have hu : IsUnit (v i) := (crd_isUnit_iff i hx).2 h
  have h' := (crd_isUnit_iff i hx').1 hu
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i hi₀
  refine eq_of_valHom_eq x x' _ hA h h' (RingHom.eq_of_eqOn_set_dense hc ?_)
  rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
  · rw [valHom_constFn, valHom_constFn]
    simp only [hp]
  · have e := (crd_ratio hx (hr j) h).symm.trans (crd_ratio hx' (hr j) h')
    rw [valR_eq x _ h, valR_eq x' _ h'] at e
    exact hu.mul_right_cancel e

end GlobalTheory.ZH.ImmSep
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericExtend

theorem eq_of_valR_eq {Y : Scheme.{0}} [IsReduced Y] {V : Y.Opens} {f g : Γ(Y, V)}
    (H : ∀ x ∈ V, ∃ (K : Type) (_ : Field K) (h : Sp K ⟶ Y), (∀ o, h o = x) ∧
      valR h V f = valR h V g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  exfalso
  have hxV := Y.basicOpen_le _ hx
  obtain ⟨K, _, h, ho, hv⟩ := H x hxV
  have h₁ : ⊤ ≤ h ⁻¹ᵁ V := fun o _ ↦ show h o ∈ V from (ho o).symm ▸ hxV
  have h₂ := (Points.le_preimage_basicOpen_iff h h₁ (f - g)).1
    fun o _ ↦ show h o ∈ Y.basicOpen (f - g) from (ho o).symm ▸ hx
  rw [Points.valR_eq h V h₁, Points.valR_eq h V h₁] at hv
  rw [Points.valR_eq h V h₁, map_sub, hv, sub_self] at h₂
  exact not_isUnit_zero h₂

theorem compat_of_valF {Q Y : Scheme.{0}} [IsReduced Q] {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ}
    (H : ∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ Q), Set.range (h ≫ J) ⊆ N.U a →
      Set.range (h ≫ J) ⊆ N.U b →
      valF h _ (τ a).val = valF (h ≫ J) _ (N.g a b).val * valF h _ (τ b).val) :
    Compat N J τ := by
  intro Z r z a b ha hb
  have l₁ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U a := J.preimage_mono inf_le_left
  have l₂ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U b := J.preimage_mono inf_le_right
  have key : res l₁ (τ a) = pullU J _ (N.g a b) * res l₂ (τ b) := by
    refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Q.residueField x, inferInstance,
      Q.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
    have ho : ∀ o, (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) o = x :=
      fun o ↦ Scheme.fromSpecResidueField_apply x o
    generalize (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) = h at ho
    have h₁ : ⊤ ≤ h ⁻¹ᵁ J ⁻¹ᵁ (N.U a ⊓ N.U b) := fun o _ ↦
      show h o ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) from (ho o).symm ▸ hx
    have := H a b _ h (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).1)
      (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).2)
    rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp,
      ← Points.valR_res h l₁ h₁, ← Points.valR_res h l₂ h₁, ← Points.valR_mul _ _ h₁] at this
    exact this
  have hz : r z ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) := ⟨ha, hb⟩
  have := congrArg (gm r z _) key
  rwa [map_mul, gm_res r z l₁ hz, gm_res r z l₂ hz, gm_pull r J z _ hz] at this

theorem exists_unit_extend_of_generic : ∀ (X P : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] (j : Sp Ω ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → ∀ (p : P ⟶ X) (e : X ⟶ P) (N : LB P), e ≫ p = 𝟙 X → Smooth p → GeometricallyIntegral p → N.IsLB → ∀ τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ, (∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → Set.range (h ≫ pullback.fst p j) ⊆ N.U b → valF h _ (τ a).val = valF (h ≫ pullback.fst p j) _ (N.g a b).val * valF h _ (τ b).val) → (∀ a, ∃ u : Γ(X, e ⁻¹ᵁ N.U a)ˣ, ∀ h : Sp Ω ⟶ pullback p j, h ≫ pullback.fst p j = j ≫ e → Set.range (j ≫ e) ⊆ N.U a → valF h _ (τ a).val = valF j _ u.val) → ∃ σ : ∀ a, Γ(P, N.U a)ˣ, ∀ (a : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → valF (h ≫ pullback.fst p j) _ (σ a).val = valF h _ (τ a).val := by
  intro X P _ Ω _ j hX _ _ _ p e N he _ _ hN τ H₁ H₂
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have := DvrModel.isIntegral_of_geometricallyIntegral (IsPullback.of_hasPullback p j)
  have hτ : Compat N (pullback.fst p j) τ := compat_of_valF H₁
  choose ρ hρ using H₂
  let eU : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p j = 𝟙 _ := pullback.lift_snd _ _ _
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ Sp Ω) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
    intro Z κ z a ha
    have hle : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ N.U a := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
    have h₁ : ⊤ ≤ (𝟙 (Sp Ω) :) ⁻¹ᵁ j ⁻¹ᵁ e ⁻¹ᵁ N.U a := fun o _ ↦
      show e (j o) ∈ N.U a from Subsingleton.elim (κ z) o ▸ ha
    have key : res hle (pullU eU _ (τ a)) = pullU j _ (ρ a) := by
      refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Ω, inferInstance, 𝟙 _,
        fun o ↦ Subsingleton.elim _ _, ?_⟩)
      have := hρ a eU w (by rintro _ ⟨o, rfl⟩; exact h₁ (x := o) trivial)
      rw [Points.valF_eq_valR, Points.valF_eq_valR] at this
      refine (Points.valR_res _ hle h₁ _).trans ?_
      refine (Points.valR_comp (𝟙 _) eU _ _).symm.trans ?_
      refine Eq.trans ?_ (Points.valR_comp (𝟙 _) j _ _)
      rwa [Category.id_comp, Category.id_comp]
    have := congrArg (gm κ z _) key
    rwa [gm_res_pullU κ eU z hle ha, gm_pull κ j z _ ha] at this
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  refine ⟨fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩, fun a K _ h _ ↦ ?_⟩
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp]
  exact congrArg _ (hs a)

end GlobalTheory.GenericExtend
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_lineBundle_sections_of_unimodular_tuples : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  first | exact @GlobalTheory.TupleGlue.exists_sections | exact GlobalTheory.TupleGlue.exists_sections | (intros; apply GlobalTheory.TupleGlue.exists_sections <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_affine_refinement_splitExtCharts : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  first | exact @GlobalTheory.ZH.UFib.exists_affine_refinement | exact GlobalTheory.ZH.UFib.exists_affine_refinement | (intros; apply GlobalTheory.ZH.UFib.exists_affine_refinement <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closed_immersion_generic_unit_locus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R), IsClosedImmersion i → LocallyOfFiniteType q → QuasiCompact q → (∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) → ∃ y : Sp B ⟶ Z, y ≫ i = x) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  first | exact @GlobalTheory.GenSpread.ClosedFac.exists_lift | exact GlobalTheory.GenSpread.ClosedFac.exists_lift | (intros; apply GlobalTheory.GenSpread.ClosedFac.exists_lift <;> assumption)
end
