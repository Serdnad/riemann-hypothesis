module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FrAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsComb {k : ℕ} {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) : Prop :=
  ∀ j, σ.f j = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b l)) * (t l).f j
end
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

structure ThetaSys.Real.UTest.Geom (u : ρ.UTest p y₀) where
  pt : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
  pt_over : ∀ a, (pt a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃! a, pt a = z
  weil : ∀ a b (c : (PadicAlgCl p)ˣ),
    (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) →
    WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (u.A.L.pull (eSec u.A.A))
  rig_gen : rig.IsGen
  fr : ∀ a, FrAt (pt a)
  fr_tors : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (pt a) (fr a)
  th : SecA u.A (PadicAlgCl p) 1
  th_val : ∀ a, ValAt th (pt a) (fr a) (y₀ ⟨S.th a, S.th_mem a⟩)
  s : S.J → SecA u.A (PadicAlgCl p) S.N
  ev_val : ∀ a i, ValAt (s i) (pt a) (fr a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)
  α : LB.Gen (LB.LinComb u.A.L (K := Fin 2) ![(snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A).left,
    (snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -((1 : ℕ) : ℤ)])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr u.A.L _ _ _ _ (LB.pullGen u.A.L _ _ α (ptSecT u.A.A 1).left)
    (rigT u.A.A u.A.L rig (TFK (R := u.V) (PadicAlgCl p)) ((S.N : ℤ) - 1))
  s_zero : IsTwistPull u.A.A u.A.L (mulT u.A.A _ (ρ.n ^ ρ.k)) (snd _ u.A.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _)
    (S.N : ℤ) ((1 : ℕ) : ℤ) α th (s ρ.i₀)
  U : S.Gam → ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  U_sym : ∀ a, SymLift u.A.A u.A.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf u.A.A u.A.L S.N (U a) (s i) σ ↔ IsComb s (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) σ

def NormVal {p : ℕ} [Fact p.Prime] (π : PadicAlgCl p) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ (x : PadicAlgCl p) (q : ℚ), v x = (q : WithTop ℚ) ↔ ‖x‖ = ‖π‖ ^ (q : ℝ)
end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH

theorem gt_add_iota_sub_exist : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ g g' : GtPtF u.D.toPre (PadicAlgCl p), ∃ g'', GtPtF.IsAdd g g' g'') ∧ (∀ y, ∃ g : GtPtF u.D.toPre (PadicAlgCl p), GtPtF.IsIota y g) ∧ ∀ g h : GtPtF u.D.toPre (PadicAlgCl p), ∃ g', GtPtF.IsAdd g' h g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u
  letI := GlobalTheory.TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  exact ⟨fun g g' => ⟨g + g', (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl⟩,
    fun y => GlobalTheory.TorusExt.exists_iota u.D.tau_bimult y,
    fun g h => ⟨g - h, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (sub_add_cancel g h).symm⟩⟩

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymBaseChange

variable {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left}

theorem pushPt_injective (h : IsGrpPullback G' G f φ) {T : Over B'} {x y : T ⟶ G'}
    (e : pushPt h.1.w x = pushPt h.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_endo (h : IsGrpPullback G' G f φ) (w : G ⟶ G) [IsMonHom w] :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := by
  let w' : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hw : w'.left ≫ φ = φ ≫ w.left := h.1.lift_fst _ _ _
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over B') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply pushPt_injective h
    have a : pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := map_mul (pushHom h T) x y
    have b : pushPt h.1.w ((x ≫ w') * (y ≫ w')) = pushPt h.1.w (x ≫ w') * pushPt h.1.w (y ≫ w') :=
      map_mul (pushHom h T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, pa⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over B') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem hypS_baseChange : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  intro B B' G G' _ _ _ _ f φ L L' hL hL' h hb ⟨w, wd, hw, hwd, hs, hp, ha⟩
  obtain ⟨w', hw', pa⟩ := exists_endo h w
  obtain ⟨wd', hwd', pd⟩ := exists_endo h wd
  have hB : (L.pull φ).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (φ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 G'.left) y _ hy, map_one, gm_pull_g L φ (𝟙 G'.left) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 G'.left) y _ hy, gm_res (𝟙 G'.left) y _ hy,
        gm_res (𝟙 G'.left) y _ hy, gm_pull_g L φ (𝟙 G'.left) y I J hy.1.1 hy.1.2,
        gm_pull_g L φ (𝟙 G'.left) y J K hy.1.2 hy.2, gm_pull_g L φ (𝟙 G'.left) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply pushPt_injective h
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hs, Category.comp_id]
  · have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', w'] (L.pull φ)) := by
      let U := pushPt h.1.w (𝟙 G')
      refine LBIso.chartPull (chartPullPull L _ U.left (Category.id_comp _))
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _)) I.down) hp
    have h₂ : LBIso (cubeLB G' ![𝟙 G', w'] (L.pull φ)) (cubeLB G' ![𝟙 G', w'] L') :=
      GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _
    exact LBIso.trans hL' hB (DVR.linComb_isLB L' hL' _ _) hb
      (LBIso.trans hB (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁ h₂)
  · have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
        (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
      let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
      refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
        fin_cases i
        · exact (pa _).trans (by simp [U])
        · simp [U]) I.down)
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (pd _).trans (by simp [U])) I.down) ha
    exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
      (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end GlobalTheory.SymBaseChange
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_point_of_inter {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (i : V →+* K) (j : V →+* O) (k : K →+* C) (l : O →+* C) (hi : Function.Injective i) (hl : Function.Injective l)
    (hc : ∀ v, l (j v) = k (i v)) (hint : ∀ (a : K) (c : O), k a = l c → ∃ v, i v = a)
    {X : Scheme.{0}} (x : Sp K ⟶ X) (b : Sp O ⟶ X) (h : spMap k ≫ x = spMap l ≫ b) :
    ∃ y : Sp V ⟶ X, spMap i ≫ y = x ∧ spMap j ≫ y = b := by
  obtain ⟨U, hU, hb, -⟩ := exists_isAffineOpen_le b (le_preimage_top b)
  have hlb : ⊤ ≤ (spMap l ≫ b) ⁻¹ᵁ U := le_preimage_comp _ b hb (le_preimage_top _)
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ (spMap k ≫ x) ⁻¹ᵁ U := h ▸ hlb
    intro w _
    rw [Subsingleton.elim w (spMap k (IsLocalRing.closedPoint C))]
    exact h1 (x := IsLocalRing.closedPoint C) trivial
  have hv : ∀ f, k ((valMap x U hx).hom f) = l ((valMap b U hb).hom f) := fun f => by
    rw [← valR_eq, ← valR_eq, ← valR_spMap_comp k x U hx, ← valR_spMap_comp l b U hb, h]
  choose g hg using fun f => hint _ _ (hv f)
  let ψ : Γ(X, U) →+* V :=
    { toFun := g
      map_one' := hi (by simp only [hg, map_one])
      map_mul' := fun a c => hi (by simp only [hg, map_mul])
      map_zero' := hi (by simp only [hg, map_zero])
      map_add' := fun a c => hi (by simp only [hg, map_add (f := _)]) }
  have e1 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom i = valMap x U hx := by
    ext f
    exact hg f
  have e2 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom j = valMap b U hb := by
    ext f
    exact hl ((hc _).trans ((congrArg k (hg f)).trans (hv f)))
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e1, specMap_valMap_fromSpec]
  · rw [← Category.assoc, ← Spec.map_comp, e2, specMap_valMap_fromSpec]

theorem pushHom_inj_of_cartesian {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := fun a b e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))

theorem torsion_integral_descends : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u jV hj b hb
  haveI := u.U.gen_hom
  let k : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  have hsq : gPt p ≫ spMap jV = spMap k ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => spMap φ) (RingHom.ext hj)
  have hbw : b.left ≫ u.G.hom = spMap jV := Over.w b
  let T : Over (Sp (FractionRing u.V)) := Over.mk (spMap k)
  let wl : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (gPt p ≫ b.left) (spMap k) (by rw [Category.assoc, hbw, hsq])
  have w1 : wl ≫ pullback.fst _ _ = gPt p ≫ b.left := pullback.lift_fst _ _ _
  have w2 : wl ≫ pullback.snd _ _ = spMap k := pullback.lift_snd _ _ _
  let w : T ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk wl w2
  let W : Over.mk (T.hom ≫ jK u.V) ⟶ Over.mk (spMap jV) := Over.homMk (gPt p) hsq
  have hp := isGrpPullback_pullback u.G (jK u.V)
  have e0 : pushHom hp T w = preHom W b := Over.OverMorphism.ext w1
  have hw : w ^ (S.r * S.N) = 1 := pushHom_inj_of_cartesian hp T (by
    rw [map_pow, e0, ← map_pow, hb, map_one, map_one])
  have hw' : (w ≫ u.U.gen.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (T.hom ≫ spMap u.yK) (pushHom u.cart T (w ≫ u.U.gen.hom))
    (by rw [← map_pow, hw', map_one])
  have ha' : (spMap k ≫ spMap u.yK) ≫ (ρ.pt a).left = (wl ≫ u.U.gen.hom.left) ≫ u.φ :=
    congrArg (fun z => z.left) ha
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hg : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd _ _ := Over.w u.U.gen.hom
  have hg' : u.U.gen.inv.left ≫ pullback.snd _ _ = u.A.A.hom := Over.w u.U.gen.inv
  have hih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.inv_hom_id
  have hhi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.hom_inv_id
  obtain ⟨x', x1, x2⟩ : ∃ x' : Sp (FractionRing u.V) ⟶ u.A.A.left,
      x' ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ x' ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa, Category.id_comp]; exact Category.comp_id _), u.cart.1.lift_fst _ _ _,
      u.cart.1.lift_snd _ _ _⟩
  have hx' : spMap k ≫ x' = wl ≫ u.U.gen.hom.left := by
    refine u.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, x1, ← Category.assoc]
      exact ha'
    · rw [Category.assoc, x2, Category.comp_id, Category.assoc]
      exact ((congrArg (wl ≫ ·) hg).trans w2).symm
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) := x' ≫ u.U.gen.inv.left
  have hx : spMap k ≫ x = wl := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.U.gen.inv.left) hx').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (wl ≫ ·) hhi).trans (Category.comp_id _))
  have hxs : x ≫ pullback.snd _ _ = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hg').trans x2)
  obtain ⟨hV, h1, h2⟩ := exists_point_of_inter (algebraMap u.V (FractionRing u.V)) jV k (OO p).subtype
    (IsFractionRing.injective _ _) Subtype.val_injective hj
    (fun a c e => (u.norm_le a).1 ((mem_OO_iff _).1 (by
      have e' : algebraMap _ (PadicAlgCl p) a = c := e
      rw [e']; exact c.2)))
    (x ≫ pullback.fst _ _) b.left (by rw [← Category.assoc, hx, w1])
  refine ⟨a, hV, x, ⟨?_, h1.symm, hxs, ?_⟩, h2⟩
  · rw [← Spec.map_preimage (hV ≫ u.G.hom), ← Spec.map_id]
    congr 1
    have h3 : Spec.preimage (hV ≫ u.G.hom) ≫ CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) =
        CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
      refine (congrArg (· ≫ u.G.hom) h1).trans ?_
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, Category.id_comp]
    ext v
    exact IsFractionRing.injective u.V (FractionRing u.V) (congrArg (fun φ => φ.hom v) h3)
  · refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (x' ≫ ·) ?_) x1)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) hih).trans (Category.id_comp _))

end GlobalTheory.ZH
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OriginFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    val (rigT A L rig T k) t z J = val rig (t ≫ T.hom) z J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) t
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hy _).trans ?_))
  exact gm_pull t T.hom z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (t ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow_origin (P : PolAV S) {T : Over S} {m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} (hx : x = 1) {τ} (H : IsTorsFrame P rig m x τ)
    (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good P.L z J) :
    val τ t z J ^ (m ^ 2) = val rig (t ≫ T.hom) z J ^ (m ^ 2) := by
  subst hx
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have q₁ := val_corr hJ hn (t ≫ T.hom)
  have q₂ := val_corr hJ hc t
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ _ hJ] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) (t ≫ T.hom) z J = val rig (t ≫ T.hom) z J ^ ((m : ℤ) ^ 2) :=
    map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L 1 τ ((m : ℤ) ^ 2)) t z J = val τ t z J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (t ≫ (1 : T ⟶ P.A).left) z J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂, q₃, zpow_one] at q₂
  rw [← zpow_natCast, ← zpow_natCast, Nat.cast_pow, q₂]
  exact inv_mul_cancel_right _ _

theorem valF_spMap_fn {R K : Type} [CommRing R] [Field K] (y : R →+* K) (a : R) :
    valF (X := (baseOver (Sp R)).left) (spMap y) ⊤ (fn a) = y a := by
  rw [valF, dite_eq_left (by simp)]
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at h'
  refine Eq.trans ?_ h'.symm
  congr 1

end GlobalTheory.OriginFrame

namespace GlobalTheory


open OriginFrame ThetaScalar in
theorem basis_value_at_origin : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (y₀ : S.R →+* K) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A → Set.range (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → ∃ ξ : K, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧ ∀ l, valF r _ ((ρ.s l).f (fun _ => jP)) = y₀ ⟨S.ev 0 l, S.ev_mem 0 l⟩ * (ξ * valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) ^ S.N := by
  intro o Ω _ _ _ S ρ K _ y₀ r jP hr hU
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := mul_left_cancel (a := ρ.pt 0) (by rw [← ρ.pt_add, add_zero, _root_.mul_one])
  let z : Sp K := IsLocalRing.closedPoint K
  let t : Sp K ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have ht : t ≫ (baseOver (Sp S.R)).hom = spMap y₀ := Category.comp_id _
  have hz : (spMap y₀ ≫ eSec ρ.P.A) z ∈ ρ.P.L.U jP := hU ⟨z, by rw [hr]⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good ρ.P.L ρ.P.isLB z (fun _ : PUnit => spMap y₀ ≫ eSec ρ.P.A) (fun _ => jP)
    (fun _ _ _ => rfl) (fun _ => hz)
  have hs : (t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, h0, ← ht, Category.assoc]; rfl
  have er : r = t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left := by
    haveI : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left :=
      inferInstanceAs (Mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, hr, hs]
  have hp := torsFrame_pow_origin ρ.P h0 (ρ.fr_tors 0) t hJ
  rw [ht] at hp
  have m₁ : r z ∈ LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hU ⟨z, rfl⟩
  have m₂ : (spMap y₀) z ∈ LB.wchart ρ.P.L (fun _ : PUnit => eSec ρ.P.A) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hz
  have m₃ := hJ.mem (fun _ : Fin 1 => (ρ.pt 0).left) t
  have a₂ : toStk z (valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) = (val ρ.rig (spMap y₀) z J).val :=
    (toStk_valF_gs (spMap y₀) _ z m₂ _).trans ((gs_unit _ z _ m₂ _).trans
      (congrArg Units.val (val_of ρ.rig (spMap y₀) z J (fun _ => jP) (fun _ => eJ PUnit.unit)).symm))
  obtain ⟨a, ha⟩ : ∃ a : K, toStk z a = (val (ρ.fr 0) t z J).val :=
    ⟨_, (toStk_valF_gs t _ z m₃ _).trans (gs_unit _ z _ m₃ _)⟩
  generalize valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val = b at a₂ ⊢
  have hb : b ≠ 0 := fun e => (val ρ.rig (spMap y₀) z J).ne_zero (by rw [← a₂, e, map_zero])
  have hab : a ^ ((S.r * S.N) ^ 2) = b ^ ((S.r * S.N) ^ 2) := (toStk z).injective (by
    rw [map_pow, map_pow, ha, a₂, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hp)
  refine ⟨a / b, by rw [div_pow, hab, div_self (pow_ne_zero _ hb)], fun l => (toStk z).injective ?_⟩
  have hv := sval_valueAt (ρ.ev_val l 0) t hJ
  have p : val (powFrame ρ.P.A ρ.P.L (ρ.pt 0) (ρ.fr 0) S.N) t z J = val (ρ.fr 0) t z J ^ (S.N : ℤ) :=
    map_zpow _ _ _
  rw [← er, p, zpow_natCast] at hv
  replace hv := (sval_of (φ := fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (ε := fun _ => (S.N : ℤ))
    (ρ.s l) r z J (fun _ => jP) (fun _ => by rw [hr]; exact eJ PUnit.unit)).symm.trans hv
  have a₁ := toStk_valF_gs r _ z m₁ ((ρ.s l).f (fun _ => jP))
  have a₃ := toStk_valF_gs t ⊤ z trivial (fn (⟨S.ev 0 l, S.ev_mem 0 l⟩ : S.R))
  rw [valF_spMap_fn] at a₃
  refine a₁.trans (hv.trans ?_)
  rw [div_mul_cancel₀ _ hb, map_mul, map_pow, a₃, ha, Units.val_pow_eq_pow_val]

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.hasTorusWeight_iff_torusEquivariant : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  first | exact @GlobalTheory.ZH.PureWt.hasWt_iff_weight | exact GlobalTheory.ZH.PureWt.hasWt_iff_weight | (intros; apply GlobalTheory.ZH.PureWt.hasWt_iff_weight <;> assumption)
end
