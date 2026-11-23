module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartGeneratorPullbackGeneratesFibre
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle018
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle001
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle018
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.LiftUnique

theorem cube_rig_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F))
    (hw : w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (m.rigPull L.L L.rig))
    (hw' : w'.IsGen ∧ LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
      (m'.rigPull L'.L L'.rig)) :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F),
      (w''.IsGen ∧ LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
        (n.rigPull L.L L.rig)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        n.F (r z) ∈ L.L.U j → m'.F (r z) ∈ L'.L.U i → r z ∈ L''.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.F) z j i * gw w' r z i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  have g := (isGen_iff w).1 hw.1
  have g' := (isGen_iff w').1 hw'.1
  have r := (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L)
    (fun _ => rfl)).1 hw.2
  have r' := (maps_iff w' _ (fun _ => eSec G') _ L''.rig L'.rig m'.e _ (rigPull_le m'.F m'.e m'.e_comm L'.L)
    (fun _ => rfl)).1 hw'.2
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  exact ⟨w'', ⟨(isGen_iff w'').2 (T.pgen_comp L'.isLB g g'),
    (maps_iff w'' _ (fun _ => eSec G) _ L''.rig L.rig (m'.e ≫ m.e) _ (rigPull_le _ _ hec L.L) (fun _ => rfl)).2
      (T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r')⟩, T⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rig_comp {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m : SABMap t₁ t f)
    (m' : SABMap t₂ t₁ (𝟙 S')) (n : SABMap t₂ t f) (hF : n.φ = m'.φ ≫ m.φ)
    (w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)) (w' : LB.Iso t₂.PP.L (t₁.PP.L.pull m'.φ)) (hw : RigIso m w)
    (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t₂.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t₂.G.left) (z : Z) (j : t.PP.L.ι) (i : t₁.PP.L.ι) (k : t₂.PP.L.ι),
        n.φ (r z) ∈ t.PP.L.U j → m'.φ (r z) ∈ t₁.PP.L.U i → r z ∈ t₂.PP.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.φ) z j i * gw w' r z i k :=
  cube_rig_comp m.cm m'.cm n.cm hF (by rw [n.base, m.base, m'.base]; exact (Category.id_comp f).symm) _ _ _ w w' hw hw'

theorem exists_over_id {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = 𝟙 _ ≫ f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ m' : SABMap t₂ t₁ (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f (𝟙 _) m n

theorem exists_hom {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ ψ : t₁.G ⟶ t₂.G, IsMonHom ψ ∧ ψ.left ≫ n.φ = m.φ := by
  subst e
  obtain ⟨ψ, h₁, h₂, -⟩ := sabMap_iso m n rfl rfl
  exact ⟨ψ.hom, h₁, h₂⟩

theorem lieComb_map {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb c (fun j => v j ≫ ψ) (w ≫ ψ) := by
  obtain ⟨u, hu, rfl⟩ := h
  have hL : ∀ L : List (epsR R ⟶ G), (L.map (· ≫ ψ)).prod = L.prod ≫ ψ := by
    intro L
    induction L with
    | nil => simp [MonObj.one_comp]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.mul_comp]
  refine ⟨fun j => u j ≫ ψ, fun j => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu j, Category.assoc]
  · rw [← hL, List.map_ofFn]
    rfl

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R}
  {x : Sp R ⟶ Xo.X}

theorem xF_eq (Λ Λ' : M.Lift f x) : Λ'.xF = Λ.xF := by
  apply pullback.hom_ext
  · exact Λ'.xF_fst.trans Λ.xF_fst.symm
  · exact Λ'.xF_snd.trans Λ.xF_snd.symm

theorem vec (Λ Λ' : M.Lift f x) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (h : Λ.Vec cv w) :
    Λ'.Vec cv w := by
  obtain ⟨ψ, hψ, e⟩ := exists_hom (xF_eq Λ Λ') Λ.m' Λ'.m'
  obtain ⟨v', u', h₁, h₂, h₃⟩ := h
  have e₁ : ψ.left ≫ Λ'.m1.φ = Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : ψ.left ≫ Λ'.m2.φ = Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  refine ⟨fun j => v' j ≫ ψ, u' ≫ ψ, fun j => ?_, lieComb_map ψ h₂, ?_⟩
  · rw [Over.comp_left, Category.assoc, e₂, h₁ j]
  · rw [Over.comp_left, Category.assoc, e₁, h₃]

theorem thTie (Λ Λ' : M.Lift f x) (s : LB.Sec (PPx x)) (h : Λ.ThTie s) : Λ'.ThTie s := by
  obtain ⟨n, e⟩ := exists_over_id ((xF_eq Λ Λ').trans (Category.id_comp _).symm) Λ.m' Λ'.m'
  have e₁ : Λ'.m1.φ = n.φ ≫ Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : Λ'.m2.φ = n.φ ≫ Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, c2, c1⟩ := h
  obtain ⟨w0, g0, r0, -⟩ := n.lin
  obtain ⟨w1', r1', T1⟩ := rig_comp Λ.m1 n Λ'.m1 e₁ w1 w0 r1 ⟨g0, r0⟩
  obtain ⟨w2', r2', T2⟩ := rig_comp Λ.m2 n Λ'.m2 e₂ w2 w0 r2 ⟨g0, r0⟩
  have hL := Λ.t'.PP.isLB
  have hL' := Λ'.t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) hL hL' σ
  obtain ⟨s1', hs1⟩ := thf_secUp ((isGen_iff w1').1 r1'.1) Xo.univ.t.PP.isLB hL' σ'
  refine ⟨w1', w2', σ', s1', r1', r2', fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => ?_,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun g hs hf (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    have hm : Λ.m2.φ (n.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) e₂).mp (h₁ hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) ⊓
        ((Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U i) := ⟨hm, mem_pull.2 hm.2, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (c2 j i _ inf_le_left inf_le_right)
    have a' : gs ((𝟙 _ ≫ n.φ) ≫ Λ.m2.φ) y _ (M.θ j) =
        (gw w2 (𝟙 _ ≫ n.φ) y j i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_appLE Λ.m2.φ _ _ _ _ y hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hz _).trans (gs_unit _ y _ hz.2 _)) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi (h₂ hy).2
    have t := T2 _ (𝟙 _) y j i k (h₁ hy).2 hi (h₂ hy).2
    refine (gs_appLE Λ'.m2.φ _ _ h₁ (𝟙 _) y hy _).trans ?_
    refine (congrArg (fun q => gs q y _ (M.θ j))
      (show 𝟙 _ ≫ Λ'.m2.φ = (𝟙 _ ≫ n.φ) ≫ Λ.m2.φ by rw [e₂, Category.assoc])).trans (a'.trans ?_)
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_unit _ y _ (h₂ hy) _).trans (congrArg Units.val t))) (gs_res _ y _ hy _)).trans ?_))
    rw [Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm
  · let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let q : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have qf : q ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have qs : q ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hq : n.φ ≫ q = g := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (fst (Over.mk x) A).left = g ≫ (fst (Over.mk x) A).left
        rw [qf, hf]
        exact n.cart.1.w.trans (Category.comp_id _)
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (snd (Over.mk x) A).left = g ≫ (snd (Over.mk x) A).left
        rw [qs, hs, e₁]
    have le : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun z hz =>
      Set.mem_iInter.2 fun _ => (congrArg (fun p => p z ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) qs).mpr (mem_pull.1 hz)
    obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    have hm : Λ.m1.φ (n.φ y) ∈ Xo.univ.t.PP.L.U (j PUnit.unit) :=
      (congrArg (fun p => p y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) e₁).mp (mem_pull.1 hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ⊓ Λ.t'.PP.L.U i := ⟨mem_pull.2 hm, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (i1 j i)
    have a' : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) =
        (gw w1 (𝟙 _ ≫ n.φ) y (j PUnit.unit) i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi hk
    have t := T1 _ (𝟙 _) y (j PUnit.unit) i k (mem_pull.1 hy) hi hk
    have d : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = gs (𝟙 _ ≫ g) y _ (s.f (fun _ => j PUnit.unit)) :=
      (congrArg (gs (𝟙 _ ≫ n.φ) y _) (c1 q qs qf j le)).trans ((gs_appLE q _ _ le _ y hz.1 _).trans
        (congrArg (fun p => gs p y _ (s.f (fun _ => j PUnit.unit))) (by rw [Category.assoc, hq])))
    refine (hs1 _ (𝟙 _) y j k hy hk).trans (Eq.trans ?_ (a'.symm.trans (d.trans (gs_appLE g _ _ hj (𝟙 _) y hy _).symm)))
    rw [t, Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm

theorem lift_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ Λ'
  exact ⟨vec Λ Λ', thTie Λ Λ'⟩

end GlobalTheory.Reg.LiftUnique
end
end

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.LiftBaseChange

section Bundles

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {F'' : X'' ⟶ X}

def IsCompIso (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (w'' : LB.Iso L'' (L.pull F'')) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : L.ι) (i : L'.ι) (k : L''.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i →
    f y ∈ L''.U k → gw w'' f y j k = gw w (f ≫ F') y j i * gw w' f y i k

theorem tie_comp (hL' : L'.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')}
    {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (V : X.Opens) (θ : ∀ j, Γ(X, V ⊓ L.U j))
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (h : ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (V ⊓ L.U j))
      (h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k),
      (F.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k))
    (j : L.ι) (k : L''.ι) (W : X''.Opens) (h₁ : W ≤ F'' ⁻¹ᵁ (V ⊓ L.U j))
    (h₂ : W ≤ (L.pull F'').U (fun _ => j) ⊓ L''.U k) :
    (F''.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w''.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k) := by
  subst e
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
  have hj : F (F' y) ∈ V ⊓ L.U j := h₁ hy
  have hk : y ∈ L''.U k := (h₂ hy).2
  let W₀ : X'.Opens := F ⁻¹ᵁ (V ⊓ L.U j) ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U i)
  have hW : (𝟙 X'' ≫ F') y ∈ W₀ := ⟨hj, mem_pull.2 hj.2, hi⟩
  have e₀ := congrArg (gs (𝟙 X'' ≫ F') y W₀) (h j i W₀ inf_le_left inf_le_right)
  have e₁ : gs ((𝟙 X'' ≫ F') ≫ F) y _ (θ j) = (gw w (𝟙 X'' ≫ F') y j i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
    (gs_appLE F _ _ _ _ y hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hW _).trans (gs_unit _ y _ hW.2 _)) (gs_res _ y _ hW _))))
  have e₂ := hσ _ (𝟙 X'') y i k hi hk
  have e₃ := T _ (𝟙 X'') y j i k hj.2 hi hk
  refine (gs_appLE _ _ _ h₁ (𝟙 _) y hy _).trans (Eq.trans ?_ (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y h₂ hy _).trans (gs_unit _ y _ (h₂ hy) _)) (gs_res _ y _ hy _)))))
  rw [← Category.assoc, e₁, e₂, ← _root_.mul_assoc, ← Units.val_mul, ← e₃]
  rfl

theorem isoMaps_comp (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)}
    {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (g : w''.IsGen)
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (s : LB.Sec (L.pull F)) (hs : IsoMaps w σ s) :
    ∃ s' : LB.Sec (L.pull F''), IsoMaps w'' σ' s' ∧ ∀ (J : PUnit → L.ι) (y : X''), y ∈ (L.pull F'').U J →
      gs (𝟙 X'') y _ (s'.f J) = gs (𝟙 X'' ≫ F') y _ (s.f J) := by
  subst e
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w'').1 g) hL hL'' σ'
  refine ⟨s', fun (i : PUnit → L.ι) k => fn_ext fun y hy => ?_, fun J y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs' _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
    obtain ⟨k, hk⟩ := exists_chart hL'' y
    have hj : F (F' y) ∈ L.U (J PUnit.unit) := mem_pull₂.1 hy
    have hW : (𝟙 X'' ≫ F') y ∈ (L.pull F).U J ⊓ L'.U i := ⟨mem_pull.2 hj, hi⟩
    have e₀ := congrArg (gs (𝟙 X'' ≫ F') y _) (hs J i)
    have e₁ : gs (𝟙 X'' ≫ F') y _ (s.f J) =
        (gw w (𝟙 X'' ≫ F') y (J PUnit.unit) i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
      (gs_res _ y _ hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
        (gs_unit _ y _ hW _) (gs_res _ y _ hW _))))
    rw [e₁, hσ _ (𝟙 X'') y i k hi hk, ← _root_.mul_assoc, ← Units.val_mul, ← T _ (𝟙 X'') y _ i k hj hi hk]
    exact hs' _ (𝟙 _) y J k hy hk

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) :
    RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

theorem rigIso_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t h) (eh : h = g ≫ f)
    (eφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ)}
    (hw : RigIso m w) (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧ IsCompIso w w' w'' := by
  have ee : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, eh]
  simp only [rigIso_iff] at hw hw' ⊢
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, li⟩ := n
  dsimp only [SABMap.φ] at ee eφ
  subst ee eφ
  obtain ⟨w'', T⟩ := exists_comp t'.PP.isLB w w' hw.1 hw'.1 t.PP.isLB t''.PP.isLB
  exact ⟨w'', ⟨T.pgen_comp t'.PP.isLB hw.1 hw'.1, T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) hw.2 hw'.2⟩, T⟩

theorem exists_comp' {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m : SABMap t' t f) (m' : SABMap t'' t' g) (h : S'' ⟶ S) (eh : h = g ≫ f) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst eh
  exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem exists_vec_lift {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {G : Over (Sp R)} {G' : Over (Sp S)}
    {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom (spMap ψ)) (v : epsR R ⟶ G) :
    ∃ v' : epsR S ⟶ G', v'.left ≫ φ = spMap (Chart.dualMapR ψ) ≫ v.left := by
  have w : (spMap (Chart.dualMapR ψ) ≫ v.left) ≫ G.hom = (epsR S).hom ≫ spMap ψ := by
    rw [Category.assoc, Over.w v]
    exact LieCombBaseChange.dualMap_over ψ
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

end GlobalTheory.LiftBaseChange

namespace GlobalTheory

open LiftBaseChange



theorem lift_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ S _ _ ψ
  obtain ⟨t'', p⟩ : ∃ t'' : SAB H (Sp S), Nonempty (SABMap t'' Λ.t' (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) Λ.t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨p⟩ := p
  have e2 : spMap (ψ.toRingHom.comp f) ≫ M.hU.fromSpec = spMap ψ.toRingHom ≫ spMap f ≫ M.hU.fromSpec := by
    rw [spMap_comp', Category.assoc]
  obtain ⟨n', hn'⟩ := exists_comp' Λ.m' p _ rfl
  obtain ⟨n1, hn1⟩ := exists_comp' Λ.m1 p _ rfl
  obtain ⟨n2, hn2⟩ := exists_comp' Λ.m2 p _ e2
  refine ⟨⟨spMap ψ.toRingHom ≫ Λ.xF, by rw [Category.assoc, Λ.xF_fst], ?_, by rw [Category.assoc, Λ.xF_j, e2],
    t'', n', n1, n2, by rw [hn1, hn', Λ.liftedChartMap_eq, Category.assoc], by rw [hn2, hn', Λ.matrix_two_by_two_congr, Category.assoc]⟩, ?_, ?_⟩
  · rw [Category.assoc, Λ.xF_snd, ← spMap_comp']
    exact congrArg spMap ψ.comp_algebraMap
  · rintro cv w ⟨v, u, hv, hc, hu⟩
    choose v' hv' using fun j => exists_vec_lift ψ.toRingHom p.cart.1 (v j)
    obtain ⟨u', hu'⟩ := exists_vec_lift ψ.toRingHom p.cart.1 u
    refine ⟨v', u', fun j => ?_, (lieComb_baseChange R S ψ.toRingHom _ _ _ p.cart _ v u cv v' u' hv' hc).1 hu', ?_⟩
    · show (v' j).left ≫ n2.φ = _
      rw [hn2, ← Category.assoc, dualMapR_comp, spMap_comp', Category.assoc (spMap _), ← hv j]
      exact (congrArg (· ≫ Λ.m2.φ) (hv' j)).trans (Category.assoc _ _ _)
    · show u'.left ≫ n1.φ = _
      rw [hn1, ← Category.assoc, ← hu]
      exact (congrArg (· ≫ Λ.m1.φ) hu').trans (Category.assoc _ _ _)
  · rintro s s' pm hp₁ hp₂ hps ⟨w1, w2, σ, s1, r1, r2, hI, hθ, hg⟩
    obtain ⟨w0, g0, r0, -⟩ := p.lin
    have R0 : RigIso p w0 := ⟨g0, r0⟩
    obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) Λ.t'.PP.isLB t''.PP.isLB σ
    obtain ⟨w1', r1', T1⟩ := rigIso_comp Λ.m1 p n1 rfl hn1 r1 R0
    obtain ⟨w2', r2', T2⟩ := rigIso_comp Λ.m2 p n2 e2 hn2 r2 R0
    obtain ⟨s1', hI', hs1'⟩ := isoMaps_comp Xo.univ.t.PP.isLB Λ.t'.PP.isLB t''.PP.isLB hn1 T1 r1'.1 σ σ' hσ' s1 hI
    refine ⟨w1', w2', σ', s1', r1', r2', hI', tie_comp Λ.t'.PP.isLB hn2 T2 _ M.θ σ σ' hσ' hθ, ?_⟩
    intro g' e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj
    have e₁' : g' ≫ (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = n1.φ := e₁
    have e₂' : g' ≫ (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = t''.G.hom := e₂
    let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let g : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have gf : g ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have gs' : g ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have sq : p.φ ≫ g = g' ≫ pm := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (fst (Over.mk x) A).left = g' ≫ pm ≫ (fst (Over.mk x) A).left
        rw [gf, hp₂, ← Category.assoc, e₂']
        exact p.cart.1.w
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (snd (Over.mk x) A).left = g' ≫ pm ≫ (snd (Over.mk x) A).left
        rw [gs', hp₁, e₁', hn1]
    have le₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) gs').mpr (mem_pull.1 hy)
    have le₂ : (PPx (spMap ψ.toRingHom ≫ x)).U (fun _ => j PUnit.unit) ≤ pm ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) :=
      fun y hy => Set.mem_iInter.2 fun _ =>
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hp₁).mpr (Set.mem_iInter.1 hy 0)
    refine fn_ext fun y hy => ?_
    have hy₁ : (𝟙 _ ≫ p.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j :=
      mem_pull.2 ((congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hn1).mp (mem_pull.1 hy))
    have c₁ : (𝟙 _ ≫ p.φ) ≫ g = (𝟙 _ ≫ g') ≫ pm := by rw [Category.id_comp, Category.id_comp, sq]
    refine (hs1' j y hy).trans ((congrArg (gs (𝟙 _ ≫ p.φ) y _) (hg g gs' gf j le₁)).trans
      ((gs_appLE g _ _ le₁ _ y hy₁ _).trans ((congrArg (fun q => gs q y _ (s.f (fun _ => j PUnit.unit))) c₁).trans ?_)))
    exact (gs_appLE pm _ _ le₂ (𝟙 _ ≫ g') y (hj hy) _).symm.trans
      ((congrArg (gs (𝟙 _ ≫ g') y _) (hps _ le₂)).trans (gs_appLE g' _ _ hj (𝟙 _) y hy _).symm)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_chart_generator_pullback_generates_fibre : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∃ s : LB.Sec (PPx x), Λ.ThTie s ∧ ∀ s' : LB.Sec (PPx x), ∃! a : R, ∀ i, s'.f i = scal x a i * s.f i := by
  first | exact @GlobalTheory.Reg.ChartGenerator.exists_thTie_generator | exact GlobalTheory.Reg.ChartGenerator.exists_thTie_generator | (intros; apply GlobalTheory.Reg.ChartGenerator.exists_thTie_generator <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_modelChart_genericPoint_component : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  first | exact @GlobalTheory.GenericChart.exists_chart_genPt | exact GlobalTheory.GenericChart.exists_chart_genPt | (intros; apply GlobalTheory.GenericChart.exists_chart_genPt <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.im_neg_of_frame_period_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → ∀ x ∈ X.dom, ∀ P : D.La →+ (Fin g → ℂ), (∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) → IsPeriod D (fun j => relab c σ (e j).1) P → r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0 := by
  first | exact @GlobalTheory.FrameSign.im_neg_of_isPeriod | exact GlobalTheory.FrameSign.im_neg_of_isPeriod | (intros; apply GlobalTheory.FrameSign.im_neg_of_isPeriod <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.integral_elements_generic_linear_section_gauss_point : ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] (f : Ω →+* U) (D N : ℕ), Algebra.trdeg K Ω = D → ∀ (v : Valuation U (WithZero (Multiplicative ℤ))) (t : Fin (D + 1) × Fin N → U) (x : Fin N → Ω), (∃ k, x k ≠ 0) → (∀ i : Fin D, ∑ k, t (i.succ, k) * f (x k) = 0) → (∀ p, v (t p) ≤ 1) → (∀ p : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) → (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) → v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) t p) = 1) → ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range t), v g ≤ 1 → ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), v d = 1 ∧ g * d = a := by
  first | exact @GlobalTheory.GaussSection.integral_elements | exact GlobalTheory.GaussSection.integral_elements | (intros; apply GlobalTheory.GaussSection.integral_elements <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_subfield_valuation_closure' : ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U), ∃ S' : Subfield U, ∀ u, u ∈ S' ↔ ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  first | exact @GlobalTheory.exists_subfield_valuation_closure | exact GlobalTheory.exists_subfield_valuation_closure | (intros; apply GlobalTheory.exists_subfield_valuation_closure <;> assumption)
end
