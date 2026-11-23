module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle192
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle193
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle194
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_exists : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBc.main | exact GlobalTheory.CompanionTheory.Ar.LieBc.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBc.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lie_model_action_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u :=
  @_root_.PositivityTheory.Xgf.lie_model_action_base_change
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lattice_sections_affine_model : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | exact GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Linear

variable {O F F' V T : Type} [CommRing O] [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F' T] [Module F T] [IsScalarTower F F' T]

theorem mem_eigSp {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (ρ : O →+* Module.End R E) (σ : O →+* R)
    (u : E) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearIndependent_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) : LinearIndependent F' fun i => j (u i) := by
  have hs : LinearIndepOn F id (Set.range u) := hu.linearIndepOn_id
  let b := Module.Basis.extend hs
  let g : Fin n → (hs.extend (Set.subset_univ _)) := fun i => ⟨u i, hs.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun a c e => hu.injective (congrArg Subtype.val e)
  have e : (fun i => j (u i)) = (hj.basis b) ∘ g := by
    funext i
    simp [IsBaseChange.basis_apply, b, g]
  rw [e]
  exact (hj.basis b).linearIndependent.comp g hg

theorem equiv_baseChange {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) (a : O) (y : F' ⊗[F] V) :
    hj.equiv (LinearMap.baseChange F' (ρ a - σ a • LinearMap.id) y) =
      ρ' a (hj.equiv y) - algebraMap F F' (σ a) • hj.equiv y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, hact, smul_comm (algebraMap F F' (σ a)) c,
      ← smul_sub]
    congr 1
    simp [algebraMap_smul]
  | add y z hy hz =>
    simp only [map_add (f := _), hy, hz, smul_add]
    abel

theorem exists_sum_of_mem_eigSp {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {t : T}
    (ht : t ∈ eigSp ρ' ((algebraMap F F').comp σ)) :
    ∃ (J : Type) (B : J → F') (b : J →₀ V), (∀ k, b k ∈ eigSp ρ σ) ∧ t = b.sum fun k w => B k • j w := by
  classical
  let B := Module.Basis.ofVectorSpace F F'
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_left B (hj.equiv.symm t)
  refine ⟨_, B, b, fun k => (mem_eigSp ρ σ _).2 fun a => ?_, ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : V →ₗ[F] V, A = ρ a - σ a • LinearMap.id := ⟨_, rfl⟩
    have h0 : LinearMap.baseChange F' A (hj.equiv.symm t) = 0 := by
      apply hj.equiv.injective
      rw [hA, equiv_baseChange hj σ hact, LinearEquiv.apply_symm_apply, map_zero]
      exact sub_eq_zero.2 ((mem_eigSp ρ' _ t).1 ht a)
    rw [← hb, map_finsuppSum] at h0
    simp only [LinearMap.baseChange_tmul] at h0
    have h1 : (b.mapRange A (map_zero A)).sum (fun i n => B i ⊗ₜ[F] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h0
    have h2 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h1
    have h3 := DFunLike.congr_fun h2 k
    simpa [hA, sub_eq_zero] using h3
  · rw [← hj.equiv.apply_symm_apply t, ← hb, map_finsuppSum]
    simp [hj.equiv_tmul]

theorem frame_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) (hs : Submodule.span F (Set.range u) = eigSp ρ σ) :
    LinearIndependent F' (fun i => j (u i)) ∧
      Submodule.span F' (Set.range fun i => j (u i)) = eigSp ρ' ((algebraMap F F').comp σ) := by
  refine ⟨linearIndependent_base hj hu, le_antisymm (Submodule.span_le.2 ?_) fun t ht => ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hi : u i ∈ eigSp ρ σ := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    refine (mem_eigSp ρ' _ _).2 fun a => ?_
    rw [hact, (mem_eigSp ρ σ _).1 hi a, map_smul]
    simp [algebraMap_smul]
  · obtain ⟨J, B, b, hb, rfl⟩ := exists_sum_of_mem_eigSp hj σ hact ht
    have key : ∀ w ∈ Submodule.span F (Set.range u),
        j w ∈ Submodule.span F' (Set.range fun i => j (u i)) := fun w hw => by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add w z _ _ hw hz =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hw hz
      | smul c w _ hw =>
        rw [map_smul, ← algebraMap_smul F' c]
        exact Submodule.smul_mem _ _ hw
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key _ (hs ▸ hb k))

end Linear

theorem eigFrame_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {F F' : Type} [Field F]
    [Field F'] [Algebra F F'] (x : Sp F ⟶ S) {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt (spMap (algebraMap F F') ≫ x) ⟶ G))
    (hv : ∀ i, (v' i).left = spMap (dualMap (algebraMap F F')) ≫ (v i).left) (h : IsEigFrame act x σ v) :
    IsEigFrame act (spMap (algebraMap F F') ≫ x) ((algebraMap F F').comp σ) v' := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨T, _, _, _, _, M', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G F F' x V M
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G F x V M P act.act act.hom act.one act.mul act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act S G F' _ T M' P act.act act.hom act.one act.mul act.add
  have hl' : ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap F F')) ≫ (M.pt e).left := fun e => by
    have := hl e
    simpa using this
  have hact : ∀ a e, ρ' a (j e) = j (ρ a e) := fun a e => M'.inj (Over.OverMorphism.ext (by
    rw [hρ' a (j e), Over.comp_left, hl', hl', hρ a e, Over.comp_left, Category.assoc]))
  choose u hu using fun i => M.onto (v i) (h.1 i).1
  obtain rfl : (fun k => M.pt (u k)) = v := funext hu
  obtain ⟨-, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S F G x V M
  obtain ⟨hli, hsp⟩ := ((hf P act ρ σ hρ).2 n u).1 h
  have hvv : v' = fun k => M'.pt (j (u k)) := funext fun k => Over.OverMorphism.ext (by rw [hv k, hl'])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action S F' G _ T M').2 P act ρ' _ hρ').2 n _).2 (frame_base hj σ hact hli hsp)

theorem isEigFrame_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  intro S G _ _ F _ x _ P _ act σ F' _ f x' hx n v v' hv h
  letI := f.toAlgebra
  subst hx
  exact eigFrame_base x act σ v v' hv h

end GlobalTheory.CompanionTheory.Ar.EigBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RiemGram

theorem hodgeForm_of_isHodgeGram {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {x : Sp ℂ ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} {Γ : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM : (L.pull ψ).IsLB := LB.isLB_pull hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

theorem isTanAt_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) (v : epsAt (spMap f) ⟶ G)
    (hv : v.left = spMap (dualMap f) ≫ (M.pt e).left) : IsTanAt G (spMap f) v := by
  have ht := M.tan e
  unfold IsTanAt at ht ⊢
  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    simp [dualMap]
  rw [hv, ← Category.assoc, hsq, Category.assoc, ht]
  let F : Over.mk (spMap f) ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk (spMap f) (by simp)
  have h1 : F ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
  exact congrArg CommaMorphism.left h1

theorem exists_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) :
    ∃ v : epsAt (spMap f) ⟶ G, v.left = spMap (dualMap f) ≫ (M.pt e).left := by
  have hsq : spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨Over.homMk (spMap (dualMap f) ≫ (M.pt e).left) ?_, rfl⟩
  have hw := Over.w (M.pt e)
  show (spMap (dualMap f) ≫ (M.pt e).left) ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f
  rw [Category.assoc, hw, ← hsq]
  simp

theorem gramAt_of_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  intro E _ _ _ H D l Xo σ n a C X t h m Ω _ ξ Li _ _ M N b x z Hm w hR hval hw
  choose v hv using fun k => exists_value C.M (C.ψ z) (x k)
  have hG := (hR N x v (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (fun e => C.ψ z (x i e))
    (fun e => C.ψ z (x j e))) hv).2 fun _ _ => rfl
  have hF := hodgeForm_of_isHodgeGram C.t.PP.isLB (fun k => isTanAt_value C.M (C.ψ z) (x k) (v k) (hv k)) hG
  have e : ∀ k, (w k).left = (v k).left ≫ m.φ := fun k => by rw [hw k, hv k, Category.assoc]
  exact ⟨w, hval, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H X t (Sp C.R) C.t h m (spMap (C.ψ z)) (v p) (v q) (w p) (w q) _
    (e p) (e q)).1 (hodgeInnerProduct_iff_hodgeForm.2 (hF q p))⟩

end GlobalTheory.CompanionTheory.Ar.RiemGram
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.frame_coordinates_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.uniformization_dim_eq_pp_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (M : LB A.left) (g : ℕ) (u : HolUnif A M g), IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → D.g = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.rank_eq_unif_dim | exact GlobalTheory.CompanionTheory.Ar.Sl.rank_eq_unif_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.rank_eq_unif_dim <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem fibreLat_of_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ), IsOver 𝔐 z κ p → FibreLat Xo.univ.t p R → FibreLat 𝔐.t z R := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p g Λ _ _ R hov hF
  obtain ⟨x, hxj, hxp, -⟩ := hov
  have hA := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Xo.univ.t Y.oF.t _ g Λ R R x).1 ⟨Y.m0.toSABMap⟩
  have hB := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Y.oF.t _ g Λ R R x).1 ⟨Y.m⟩
  have hC := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t 𝔐.t _ g Λ R R z).1 ⟨𝔐.m⟩
  rw [← hxp] at hF
  have h2 := hB.1 (hA.2 hF)
  apply hC.2
  have hj : x ≫ Y.j = z ≫ 𝔐.f := hxj
  rw [← hj]
  exact h2

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_dominant_compat : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → IsExtOver i j ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePull.main | exact GlobalTheory.CompanionTheory.Ar.LiePull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePull.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | exact GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

section Lat

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem lat_eq_span (M : LieModel G ξ E) (p : Cpt ξ)
    (hx : Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ) {r : ℕ}
    (b : Fin r → ExtE hx M) (hsp : Submodule.span (X.presheaf.stalk p.1) (Set.range b) = ⊤) :
    M.lat p = Submodule.span (regAt ξ p) (Set.range fun k => val (b k)) := by
  have car := (lieLat_carrier X G Ω ξ E M p).1
  apply le_antisymm
  · intro e he
    obtain ⟨v, hv⟩ := (car e).1 he
    let y : ExtE hx M := ⟨e, v, hv⟩
    have hy : y ∈ Submodule.span (X.presheaf.stalk p.1) (Set.range b) := by
      rw [hsp]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    have he' : e = ∑ k, genMap ξ p (c k) • val (b k) := by
      have h1 : val y = e := rfl

      rw [← h1, ← hc, map_sum]
      rfl
    rw [he']
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem _ (⟨genMap ξ p (c k), c k, rfl⟩ : regAt ξ p) (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact (car _).2 (val_spec (b k))

theorem ext_basis {A : Type} [CommRing A] [IsLocalRing A] {g : A →+* Ω} {x : Spec (CommRingCat.of A) ⟶ X}
    (hs : Smooth G.hom) (hg : Function.Injective g) (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ)
    (M : LieModel G ξ E) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) A (ExtE hx M)) :=
  GlobalTheory.T.lie_model_free_over_local_ring X G hs A x (ExtE hx M) (extModel hg hx M)

end Lat

theorem frame : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ → IsCptGen ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → Smooth G.hom → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → ∀ q' : Cpt ξ', ∃ (r : ℕ) (B : Module.Basis (Fin r) Ω E) (B' : Module.Basis (Fin r) Ω' E') (v : Fin r → (epsAt (X.fromSpecStalk (f q'.1)) ⟶ G)) (v' : Fin r → (epsAt (X'.fromSpecStalk q'.1) ⟶ G')), (∀ k, B' k = j (B k)) ∧ M.lat ⟨f q'.1, hd.specializes q'⟩ = Submodule.span (regAt ξ ⟨f q'.1, hd.specializes q'⟩) (Set.range B) ∧ M'.lat q' = Submodule.span (regAt ξ' q') (Set.range B') ∧ (∀ k, M.Extends ⟨f q'.1, hd.specializes q'⟩ (B k) (v k)) ∧ (∀ k, M'.Extends q' (B' k) (v' k)) ∧ ∀ k, (v' k).left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (v k).left := by
  intro X X' Ω Ω' _ _ ξ ξ' hξ hξ' f i hd G _ _ G' _ _ φ hG hs E _ _ M E' _ _ M' j hj q'
  have hp : genPt ξ ⤳ f q'.1 := hd.specializes q'
  have hx := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨f q'.1, hp⟩
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') q'
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap q'.1).hom) ≫ X.fromSpecStalk (f q'.1) =
      X'.fromSpecStalk q'.1 ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ' q').comp (f.stalkMap q'.1).hom = i.comp (genMap ξ ⟨f q'.1, hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd q'.1 q'.2 hp)
  have hg := hξ.inj ⟨f q'.1, hp⟩
  have hg' := hξ'.inj q'
  obtain ⟨r, ⟨b⟩⟩ := ext_basis (A := X.presheaf.stalk (f q'.1)) hs hg hx M
  obtain ⟨hli, hsp⟩ := bc hs (genMap ξ ⟨f q'.1, hp⟩) (X.fromSpecStalk (f q'.1)) ξ hx (extModel hg hx M) M b
    (fun k => val (b k)) (fun k => (vec_spec (b k)).2)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = val (b k) := fun k => by simp [B]
  obtain ⟨hli', hsp'⟩ := bc hs i ξ (ξ' ≫ f) hd.symm M (LieMove.pushModel hG M') B (fun k => j (B k)) (fun k => hj _)
  let B' : Module.Basis (Fin r) Ω' E' := Module.Basis.mk hli' hsp'.ge
  have hB' : ∀ k, B' k = j (B k) := fun k => by simp [B']
  have up : ∀ k, ∃ u : epsAt (X'.fromSpecStalk q'.1) ⟶ G',
      Ext (genMap ξ' q') (X'.fromSpecStalk q'.1) M' (j (val (b k))) u ∧
      u.left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (vec (b k)).left :=
    fun k => ext_up hG hj hρ hρ' hx' (vec_spec (b k))
  choose u hu huφ using up
  let b' : Fin r → ExtE hx' M' := fun k => ⟨j (val (b k)), u k, hu k⟩
  obtain ⟨-, hsp''⟩ := bc hs (f.stalkMap q'.1).hom (X.fromSpecStalk (f q'.1)) (X'.fromSpecStalk q'.1 ≫ f) hρ
    (extModel hg hx M) (LieMove.pushModel hG (extModel hg' hx' M')) b b'
    (fun k => by
      have e₁ : vec (b' k) = u k := (vec_spec (b' k)).unique hg' (hu k)
      show (vec (b' k)).left ≫ φ = _
      rw [e₁]
      exact huφ k)
  refine ⟨r, B, B', fun k => vec (b k), u, hB', ?_, ?_, ?_, ?_, huφ⟩
  · rw [lat_eq_span M _ hx b b.span_eq]
    congr 2
    exact funext fun k => (hB k).symm
  · rw [lat_eq_span M' q' hx' b' hsp'']
    congr 2
    exact funext fun k => by rw [hB', hB]; rfl
  · intro k
    rw [hB]
    exact vec_spec (b k)
  · intro k
    rw [hB', hB]
    exact hu k

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.gram_matrix_continuous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop <;> assumption)
end
