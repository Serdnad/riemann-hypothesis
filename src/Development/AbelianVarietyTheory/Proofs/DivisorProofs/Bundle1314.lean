module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} {f : J → X.functionField}

theorem regAt_nhds {x : X} {g : X.functionField} (h : RegAt x g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, RegAt y g := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact ⟨U, hx, fun y hy => regAt_fnOf hy _ a⟩

theorem exists_min [Fintype J] [Nonempty J] (hf : Total f) (x : X) :
    ∃ j, ∀ l, RegAt x (f l / f j) := by
  have key : ∀ s : Finset J, s.Nonempty → ∃ j, ∀ l ∈ s, RegAt x (f l / f j) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨a, fun l hl => ?_⟩
      rw [Finset.mem_singleton.1 hl, div_self (hf.1 a)]
      exact (unitAt_one x).regAt
    | cons a s ha hs ih =>
      obtain ⟨j, hj⟩ := ih
      rcases hf.2 x a j with h | h
      ·
        refine ⟨j, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · exact h
        · exact hj l hl
      ·
        refine ⟨a, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · rw [div_self (hf.1 l)]; exact (unitAt_one x).regAt
        · have e : f l / f a = f l / f j * (f j / f a) := by
            rw [div_mul_div_cancel₀ (hf.1 j)]
          rw [e]; exact (hj l hl).mul h
  obtain ⟨j, hj⟩ := key Finset.univ Finset.univ_nonempty
  exact ⟨j, fun l => hj l (Finset.mem_univ l)⟩

def inv (hf : Total f) (j : J) : X.functionFieldˣ := Units.mk0 (f j)⁻¹ (inv_ne_zero (hf.1 j))

theorem germOf_inv_eq (hf : Total f) {x : X} {j j' : J} (hj : ∀ l, RegAt x (f l / f j))
    (hj' : ∀ l, RegAt x (f l / f j')) : germOf x (inv hf j) = germOf x (inv hf j') := by
  rw [germOf_eq_iff]
  change UnitAt x ((f j')⁻¹ / (f j)⁻¹)
  rw [inv_div_inv]
  refine (unitAt_iff (div_ne_zero (hf.1 j) (hf.1 j'))).2 ⟨hj' j, ?_⟩
  rw [inv_div]
  exact hj j'

theorem isOpen_minSet [Finite J] (hf : Total f) (j : J) :
    IsOpen {y : X | ∀ l, RegAt y (f l / f j)} := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  choose V hV hV' using fun l => regAt_nhds (hy l)
  exact ⟨⋂ l, (V l : Set X), fun z hz l => hV' l z (Set.mem_iInter.1 hz l),
    isOpen_iInter_of_finite fun l => (V l).isOpen, Set.mem_iInter.2 hV⟩

variable [Fintype J] [Nonempty J]

def fsDiv (hf : Total f) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x (inv hf (exists_min hf x).choose), fun x =>
    ⟨⟨_, isOpen_minSet hf (exists_min hf x).choose⟩, (exists_min hf x).choose_spec,
      inv hf (exists_min hf x).choose, fun y hy =>
        germOf_inv_eq hf (exists_min hf y).choose_spec hy⟩⟩

theorem isEqn_inv (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).IsEqn x (inv hf j) :=
  germOf_inv_eq hf (exists_min hf x).choose_spec hj

theorem mem_sections (hf : Total f) (l : J) : f l ∈ (fsDiv hf).sections :=
  CartierDiv.mem_sections.2 fun x =>
    ⟨_, isEqn_inv hf (exists_min hf x).choose_spec, by
      change RegAt x (f l * (f _)⁻¹)
      rw [← div_eq_mul_inv]
      exact (exists_min hf x).choose_spec l⟩

theorem generatesAt (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).GeneratesAt x (f j) :=
  ⟨_, isEqn_inv hf hj, by
    change UnitAt x (f j * (f j)⁻¹)
    rw [mul_inv_cancel₀ (hf.1 j)]
    exact unitAt_one x⟩

end GlobalTheory.HSNef.FSExist

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} [Fintype J] [Nonempty J] {f : J → X.functionField}
  [DecidableEq J]

def sec (hf : Total f) (l : J) : (toLB (fsDiv hf)).Sec :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose

theorem rat_sec (hf : Total f) (l : J) : (presents_toLB (fsDiv hf)).rat (sec hf l) = f l :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose_spec

theorem iSup_sec (hf : Total f) : ⨆ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (sec hf j) = ⊤ :=
  eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨(exists_min hf x).choose,
    ((presents_toLB (fsDiv hf)).generatesAt_rat_iff _).1 (by
      rw [rat_sec]; exact generatesAt hf (exists_min hf x).choose_spec)⟩

def expDiag (w : J → ℝ) : Matrix J J ℂ := Matrix.diagonal fun j => ((Real.exp (w j) : ℝ) : ℂ)

theorem det_expDiag (w : J → ℝ) : (expDiag w).det ≠ 0 := by
  classical
  rw [expDiag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

theorem map_expDiag (w : J → ℝ) : (expDiag w).map (starRingEnd ℂ) = expDiag w := by
  ext i j
  by_cases h : i = j
  · subst h; rw [Matrix.map_apply, expDiag, Matrix.diagonal_apply_eq, Complex.conj_ofReal]
  · simp [expDiag, Matrix.diagonal_apply_ne _ h]

theorem sum_expDiag (w : J → ℝ) (v : J → ℂ) (a : J) :
    ∑ j, expDiag w j a * v j = ((Real.exp (w a) : ℝ) : ℂ) * v a := by
  classical
  rw [Finset.sum_eq_single a (fun j _ hj => by simp [expDiag, Matrix.diagonal_apply_ne _ hj])
    (fun h => (h (Finset.mem_univ a)).elim)]
  simp [expDiag]

end GlobalTheory.HSNef.FSExist


open GlobalTheory.HSNef.FSExist in
theorem GlobalTheory.HSNef.exists_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f →
      ∃ M : HermLB p, IsFS M f w := by
  intro k _ X _ p J _ _ f w hf
  classical
  let h := presents_toLB (fsDiv hf)
  refine ⟨HermLB.fs p (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (fun _ => expDiag w)
    (fun _ => det_expDiag w) (fun _ => ⟨1, one_mem _, by rw [mul_one, map_expDiag]⟩), ?_⟩
  refine ⟨fun i => i.1.2, h.isRatSec, fun x c hx => ⟨fun j => ?_, ?_⟩, fun σ y (c : (toLB (fsDiv hf)).ι) (hy : y ∈ ptsIn p σ ((toLB (fsDiv hf)).U c)) => ?_⟩
  · exact (c.2.2 x hx).regularAt_iff.1 (CartierDiv.mem_sections.1 (mem_sections hf j) x)
  · exact ⟨_, (c.2.2 x hx).generatesAt_iff.1 (generatesAt hf (exists_min hf x).choose_spec)⟩
  · refine (Weight.fsBasis_φ (p := p) (σ := σ) (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (expDiag w)
      (det_expDiag w) c y).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_expDiag]
    have e : f a * (c.1.2 : X.functionField) = fnOf _ c.2.1 ((sec hf a).f c) := by
      rw [← rat_sec hf a]; exact h.rat_mul (sec hf a) c c.2.1
    have e2 : ratVal (f a * (c.1.2 : X.functionField)) y =
        valR y.1 ((toLB (fsDiv hf)).U c) ((sec hf a).f c) := by
      rw [e]; exact ratVal_fnOf (U := (toLB (fsDiv hf)).U c) hy c.2.1 _
    rw [e2]
    rw [norm_mul, mul_pow, mul_comm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    norm_num
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_functionField_map_of_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K)
      (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt →
        ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y W K _ ψ₁ ψ₂ ζ h h₁ h₂
  have hs : ζ (IsLocalRing.closedPoint K) ⤳ genericPoint W.Z := h ▸ specializes_rfl
  let j : W.Z.functionField →+* K :=
    (W.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) ζ).hom
  have e : spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ := by
    change Spec.map (CommRingCat.ofHom j) ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo ζ
  have key : ∀ (p : W.Z ⟶ Y.X) [IsDominant p] (ψ : Y.Fn →+* K), ζ ≫ p = spMap ψ ≫ (ratOf Y).pt →
      j.comp (functionFieldMap p) = ψ := by
    intro p _ ψ hp
    have e2 : spMap (j.comp (functionFieldMap p)) ≫ Y.X.fromSpecStalk (genericPoint Y.X) =
        spMap ψ ≫ Y.X.fromSpecStalk (genericPoint Y.X) := by
      change Spec.map (CommRingCat.ofHom (j.comp (functionFieldMap p))) ≫ genericFieldPoint Y.X = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap,
        ← Category.assoc]
      change (spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z)) ≫ p = _
      rw [e, hp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e2))
  exact ⟨j, key W.p₁ ψ₁ h₁, key W.p₂ ψ₂ h₂⟩

end GlobalTheory.FlagPush
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_localEqn_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  intro X _ _ p D hD x
  obtain ⟨m, D₀, hm, hEff, rfl⟩ := hD
  obtain ⟨f, hf⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
  refine ⟨m, f, hm, CartierDiv.eff_iff.1 hEff x f hf, fun z hz E hE => ?_⟩
  rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

theorem isLogEqn_add_smul_iff_of_off {p : X ⟶ Sp k} {n : ℕ} {Γ B : X → ℚ} (c : ℚ) {x : X}
    (hB : Off B x) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    IsLogEqn p (Γ + c • B) η x m g ↔ IsLogEqn p Γ η x m g := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have : (Γ + c • B) z = Γ z := by simp [hB z hz]
  rw [this]

theorem off_add_smul (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ)
    (n : ℕ) (Γ B : X → ℚ) (c : ℚ) (x : X) (hB : Off B x) :
    (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧
      (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z := by
  have e := isLogEqn_add_smul_iff_of_off (p := p) (n := n) (Γ := Γ) c hB
  refine ⟨?_, ?_, ?_, fun z hz w hw => hB w (hw.trans hz)⟩
  · unfold KltAt
    simp only [e]
  · unfold LcAt
    simp only [e]
  · unfold IsNkltCentre
    simp only [e]

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem Dbl.p_comp_eq_of_isHom : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  intro F _ X Y φ f hf W hW
  haveI : IsDominant (W.Z.fromSpecStalk (genericPoint W.Z)) := ⟨by
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W.Z).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  haveI : IsSeparated X.str := (ratOf X).sep
  have hs : f ≫ X.str = Y.str := hf.inducedModelMorphism_comp_structureMap
  refine ext_of_isDominant_of_isSeparated X.str ?_ (W.Z.fromSpecStalk (genericPoint W.Z)) ?_
  · change (W.p₁ ≫ f) ≫ X.str = (W.p₂ ≫ f) ≫ X.str
    rw [Category.assoc, Category.assoc, hs, W.str_eq]
  · have e₁ := specMap_functionFieldMap W.p₁
    have e₂ := specMap_functionFieldMap W.p₂
    have hφ : (functionFieldMap W.p₁).comp φ.toRingHom = (functionFieldMap W.p₂).comp φ.toRingHom :=
      RingHom.ext hW
    have key : ∀ (α : Y.Fn →+* W.Z.functionField),
        Spec.map (CommRingCat.ofHom α) ≫ genericFieldPoint Y.X ≫ f =
          Spec.map (CommRingCat.ofHom (α.comp φ.toRingHom)) ≫ (ratOf X).pt := by
      intro α
      have hf' : genericFieldPoint Y.X ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hf
      rw [hf', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    change genericFieldPoint W.Z ≫ W.p₁ ≫ f = genericFieldPoint W.Z ≫ W.p₂ ≫ f
    rw [← Category.assoc, ← e₁, Category.assoc, ← Category.assoc (genericFieldPoint W.Z), ← e₂, Category.assoc,
      key, key, hφ]

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PairStep

theorem qWeil_zero_cartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem qNum_zero_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ N : LB X, QNum p N 0 0 := by
  intro X _ _ p _ N
  letI := algebraΓOfHom p
  refine ⟨1, 0, one_pos, CartierDiv.eff_zero, (qWeil_zero_cartier 1).symm, fun C _ => ?_⟩
  rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
  simp

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem shiftA_nu (P : Pair p) (u : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  have e : (shiftA P u).nu a b σ y f = ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) := rfl
  rw [e, Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem shiftA_Bl (P : Pair p) (u : ℝ) (a b : ℤ) (R : ℝ) :
    (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u)) := by
  ext f
  simp only [Pair.Bl, Set.mem_setOf_eq, shiftA_H, shiftA_nu]
  refine and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun y => ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]

theorem genAt_shiftA (P : Pair p) (u : ℝ) (c : ℕ) (h : GenAt P c) : GenAt (shiftA P u) c := by
  obtain ⟨n, v, hv, hg⟩ := h
  refine ⟨n, v, fun i => by rw [shiftA_H]; exact hv i, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hg σ y
  exact ⟨i, by rw [shiftA_nu]; exact mul_ne_zero hi (Real.exp_pos _).ne'⟩

theorem shiftA_props : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) :=
  fun _ _ _ _ _ P u => ⟨shiftA_nu P u, shiftA_Bl P u, genAt_shiftA P u⟩

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isFS_mem_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  intro k _ X _ p M J _ f w h
  obtain ⟨ρ, hρ, hreg, -⟩ := h
  refine ⟨⟨M, M, ρ, ρ, hρ, hρ⟩, rfl, fun j x i c hi _ => ?_⟩
  have e : Pair.loc ⟨M, M, ρ, ρ, hρ, hρ⟩ 1 0 (f j) i c = f j * (ρ i : X.functionField) := by
    simp [Pair.loc]
  rw [e]
  exact (hreg x i hi).1 j

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem le_iff_local : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  intro k _ X _ p A B
  have hloc : ∀ (P : Pair p) i j, P.loc 1 (-1) 1 i j = (P.r i : X.functionField) / (P.r' j : X.functionField) := by
    intro P i j
    simp [Pair.loc, div_eq_mul_inv]
  have hexp : ∀ s t : ℝ, -(((1 : ℤ) : ℝ) * s + ((-1 : ℤ) : ℝ) * t) / 2 = -(s - t) / 2 := by
    intro s t
    push_cast
    ring
  constructor
  · rintro ⟨P, rfl, rfl, hH, hnu⟩
    refine ⟨P.r, P.r', P.hr, P.hr', fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
    · rw [← hloc]
      exact hH x i j hi hj
    · have e := hnu σ y
      rw [nu_eq k X p P 1 (-1) 1 hH σ y i j hi hj, hloc, hexp] at e
      exact e
  · rintro ⟨r, r', hr, hr', hreg, hnu⟩
    refine ⟨⟨A, B, r, r', hr, hr'⟩, rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [hloc]
      exact hreg x i j hi hj
    · rw [Pair.nu, hloc, hexp]
      exact hnu σ y _ _ (mem_pick _ y) (mem_pick _ y)

end GlobalTheory.HSNef
end
end
