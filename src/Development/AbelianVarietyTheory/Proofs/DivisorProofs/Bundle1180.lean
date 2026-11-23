module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BasisChange

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def cb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) : epsR R ⟶ G :=
  ∏ i, GrpTangent.epsScale (c i) ≫ v i

theorem comb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = cb c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨fun i => GrpTangent.epsScale (c i) ≫ v i, fun i => rfl, by rw [List.prod_ofFn]; rfl⟩

theorem comp_prod' {T T' : Over (Sp R)} (s : T' ⟶ T) {J : Type} (S : Finset J) (u : J → (T ⟶ G)) :
    s ≫ ∏ i ∈ S, u i = ∏ i ∈ S, s ≫ u i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem cb_tan {n : ℕ} (c : Fin n → R) {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    IsTangent (cb c v) := by
  rw [GrpTangent.isTangent_iff, cb, comp_prod']
  exact Finset.prod_eq_one fun i _ => (GrpTangent.isTangent_iff _).1 (GrpTangent.isTangent_epsScale _ (hv i))

theorem scale_sum {w : epsR R ⟶ G} (hw : IsTangent w) {J : Type} (S : Finset J) (a : J → R) :
    GrpTangent.epsScale (∑ i ∈ S, a i) ≫ w = ∏ i ∈ S, GrpTangent.epsScale (a i) ≫ w := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GrpTangent.epsScale_zero_comp hw
  | insert j S hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, GrpTangent.epsScale_add_comp _ _ hw, ih]

theorem cb_cb {m n : ℕ} (a : Fin m → R) (M : Matrix (Fin m) (Fin n) R) {v : Fin n → (epsR R ⟶ G)}
    (hv : ∀ i, IsTangent (v i)) : cb a (fun i => cb (M i) v) = cb (Matrix.vecMul a M) v := by
  simp only [cb, comp_prod', GrpTangent.epsScale_mul_assoc]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← scale_sum (hv j)]
  rfl

theorem cb_single {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin n) :
    cb (Pi.single j 1) v = v j := by
  rw [cb, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, GrpTangent.epsScale_one, Category.id_comp]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, GrpTangent.epsScale_zero_comp (hv i)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem exists_unit {n : ℕ} {y y' : Fin n → (epsR R ⟶ G)} (hy : IsLieBasis y) (hy' : IsLieBasis y') :
    ∃ M : Matrix (Fin n) (Fin n) R, IsUnit M ∧ ∀ i, IsLieComb (M i) y (y' i) := by
  choose M hM using fun i => (hy.2 _ (hy'.1 i)).exists
  choose N hN using fun i => (hy'.2 _ (hy.1 i)).exists
  refine ⟨Matrix.of M, ?_, hM⟩
  have e : y' = fun i => cb (Matrix.of M i) y := funext fun i => (comb_iff _ _ _).1 (hM i)
  have h : Matrix.of N * Matrix.of M = 1 := by
    ext i j
    have k : y i = cb (Matrix.vecMul (N i) (Matrix.of M)) y := by
      rw [← cb_cb _ _ hy.1, ← e]
      exact (comb_iff _ _ _).1 (hN i)
    have := (hy.2 _ (hy.1 i)).unique ((comb_iff _ _ _).2 k) ((comb_iff _ _ _).2 (cb_single hy.1 i).symm)
    have := congrFun this j
    rw [Matrix.one_apply, Matrix.mul_apply]
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, eq_comm] using this
  exact IsUnit.of_mul_eq_one_right _ h

theorem basis_of_unit {n : ℕ} {v v' : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {M : Matrix (Fin n) (Fin n) R}
    (hM : IsUnit M) (h : ∀ i, IsLieComb (M i) v (v' i)) : IsLieBasis v' := by
  have e : v' = fun i => cb (M i) v := funext fun i => (comb_iff _ _ _).1 (h i)
  subst e
  refine ⟨fun i => cb_tan _ hv.1, fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hv.2 w hw
  obtain ⟨U, rfl⟩ := hM
  set M : Matrix (Fin n) (Fin n) R := U.val with hMU
  have hN : M * U.inv = 1 := U.val_inv
  have hN' : U.inv * M = 1 := U.inv_val
  have key : ∀ b, IsLieComb b (fun i => cb (M i) v) w ↔ Matrix.vecMul b M = c := fun b => by
    rw [comb_iff, cb_cb _ _ hv.1, ← comb_iff]
    exact ⟨fun q => hu _ q, fun q => by rw [q]; exact hc⟩
  refine ⟨Matrix.vecMul c U.inv, (key _).2 ?_, fun b hb => ?_⟩
  · rw [Matrix.vecMul_vecMul, hN', Matrix.vecMul_one]
  · rw [← (key b).1 hb, Matrix.vecMul_vecMul, hN, Matrix.vecMul_one]

end GlobalTheory.MBLow.BasisChange

theorem GlobalTheory.MBLow.key_basis_change : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  intro κ hκ R K _ _ _ f x G _ _ φ hφ y y' v' hy hy' hv hv'
  obtain ⟨M, hM, hMy⟩ := GlobalTheory.MBLow.BasisChange.exists_unit hy hy'
  have hc : ∀ i, IsLieComb ((M.map f) i) x.v (v' i) := fun i =>
    Chart.comb_baseChange f hφ (hMy i) hv (hv' i)
  let _ := x.P.isAb.comm
  have hb : IsLieBasis v' := GlobalTheory.MBLow.BasisChange.basis_of_unit x.basis (hM.map f.mapMatrix) hc
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  refine ⟨hb, hd.unit ^ 4, ?_⟩
  have := hκ K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne v' hb 1 (M.map f)
    (fun i => by rw [show Geo.Tor.constFn x.P.A.hom _ (1 : K) = 1 by simp [Geo.Tor.constFn], _root_.one_mul]) hc
  have e : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  rw [e] at this
  simpa using this
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivOfLam

open GlobalTheory.CechPic

theorem cls_cube_pair {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  apply _root_.GlobalTheory.PowerTangent.cls_cube_two <;> assumption

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (hf : ∀ y, f y ∈ L.U i) : pull f (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)

theorem exists_chart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : X) : ∃ i, z ∈ L.U i := by
  have : z ∈ (⊤ : X.Opens) := trivial
  rw [← hL.cover] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

theorem kTriv_of_lam_iso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (P : LB (G2 B).left), P.IsLB →
    (∀ (T : Over S) (x : T ⟶ B), (∃ t : (P.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (L : LB B.left), L.IsLB → LBIso (abelian₂ B L) P → KTriv B L := by
  intro S B _ _ _ P hP H L hL hiso R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)
  obtain ⟨V, hpV, c₀, hc₀⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hL ((1 : Over.mk t ⟶ B).left p)
  let W : (Spec (CommRingCat.of R)).Opens := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j
  refine ⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩
  let T₀ : Over S := Over.mk t
  let TW : Over S := Over.mk (W.ι ≫ t)
  let ιW : TW ⟶ T₀ := Over.homMk W.ι rfl
  suffices key : ιW ≫ x = 1 by
    have := congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)
    exact this
  refine H TW (ιW ≫ x) ?_
  let c := cls L hL
  have hLam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hTD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _

  let O : (T₀ ⊗ B).left.Opens := (fst T₀ B).left ⁻¹ᵁ V
  have h₀ : pull O.ι (cls _ hTD) = 0 := (cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩
  let N : B ⊗ TW ⟶ T₀ ⊗ B := lift (snd B TW ≫ ιW) (fst B TW)
  have hN : Set.range N.left.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T₀ B).left (N.left z) ∈ V
    have k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι := by rw [← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]
    exact ((snd B TW).left z).2.1.1
  have h₁ : pull N.left (cls _ hTD) = 0 := by
    rw [← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c := by
    refine (cls_linComb hL _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c := by
    have k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW := by
      rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]; rfl
    have k₂ : N ≫ snd T₀ B = fst B TW := lift_snd _ _
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂] at h₁
    exact sub_eq_zero.1 h₁
  have hcP : cls _ hP = cls _ hLam := ((cls_eq_iff hLam hP).2 hiso).symm
  have hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c +
      pull (1 : G2 B ⟶ B).left c := cls_cube_pair hL (fst B B) (snd B B) hLam
  have e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0 := by
    rw [Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]
    intro y
    exact y.2.1.2
  have e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0 := by
    have k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]
    intro y
    exact y.2.2
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  show pull _ (cls _ hP) = 0
  rw [hcP, hC, map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one,
    e₂, e₃, e₄]
  abel

end GlobalTheory.KTrivOfLam
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  intro R _ A B _ _ P _ φ H
  exact SymmPoincare.isCorrForm_swap H

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem rigOfOmega_injective_of_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero_of_pow p R N hN b (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

end GlobalTheory.PDivGroup
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  first | exact @GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | exact GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | (intros; apply GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ <;> assumption)
end

section

open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell

namespace GlobalTheory.GKFactor

variable {k : Type} [Field k] {n : ℕ}

theorem weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (x⁻¹).val p (w p) * x.val (w p) p = 1 := by
  have h : (x⁻¹ * x).val p p = (1 : GL (Fin n) k).val p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

theorem weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    x.val (w p) p * (x⁻¹).val p (w p) = 1 := by
  have h : (x * x⁻¹).val (w p) (w p) = (1 : GL (Fin n) k).val (w p) (w p) := by rw [mul_inv_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single p (fun b _ hb => by
      rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

theorem weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : x.val a (w⁻¹ a) ≠ 0 := by
    intro h0
    have := weylRep_mul_inv_diag hx (w⁻¹ a)
    rw [show w (w⁻¹ a) = a by simp] at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h : (x⁻¹ * x).val p (w⁻¹ a) = (1 : GL (Fin n) k).val p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

theorem weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k)
    (p q : Fin n) : (x⁻¹ * u * x).val p q = (x⁻¹).val p (w p) * u.val (w p) (w q) * x.val (w q) q := by
  have hi := weylRep_inv hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

theorem mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k) :
    u ∈ cell x ↔ u ∈ unipB k (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → u.val a b = 0 := by
  rw [mem_cell, mem_unipBLower]
  refine and_congr_right fun hu => ?_
  rw [mem_unipB] at hu
  constructor
  · rintro ⟨hl, -⟩ a b hab hw
    have h := hl _ _ hw
    rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
    have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
    have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
    rw [show w (w⁻¹ a) = a by simp] at h1
    rw [show w (w⁻¹ b) = b by simp] at h2
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
      · exact h
    · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
  · intro h
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · rw [weylRep_conj_apply hx]
      rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
      · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
      · rw [hu.1 _ _ hl, mul_zero, zero_mul]
    · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

end GlobalTheory.GKFactor
end

section

noncomputable section

open MeasureTheory

namespace GlobalTheory

namespace WeylCell

def partnerU {n : ℕ} (k : Fin (n / 2)) : Fin n :=
  if h : k.val + 1 < n / 2 then lo (⟨k.val + 1, h⟩ : Fin (n / 2)) else (lo k).rev

def simpleU {n : ℕ} (k : Fin (n / 2)) : Equiv.Perm (Fin n) :=
  if k.val + 1 < n / 2 then Equiv.swap (lo k) (partnerU k) * Equiv.swap (lo k).rev (partnerU k).rev
  else Equiv.swap (lo k) (lo k).rev

def actU {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : Fin (n / 2) → ℂˣ :=
  if h : k.val + 1 < n / 2 then α ∘ Equiv.swap k ⟨k.val + 1, h⟩ else Function.update α k (α k)⁻¹

def cSimpleU (q : ℕ) {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  if h : k.val + 1 < n / 2 then cSL ((q : ℂ) ^ 2) ((α k : ℂ) / α ⟨k.val + 1, h⟩)
  else if Even n then cSL q (α k) else cSU q (α k)

theorem IsWeylRep.inv {R : Type} [CommRing R] {n : ℕ} {v : Equiv.Perm (Fin n)} {y : GL (Fin n) R}
    (hy : IsWeylRep v y) : IsWeylRep v⁻¹ y⁻¹ := by
  have key : ∀ i j, ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (v j) *
      (y : Matrix (Fin n) (Fin n) R) (v j) j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Units.inv_mul y) i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single (v j)] at h
    · rw [h, Matrix.one_apply]
    · intro b _ hb; rw [hy b j hb, mul_zero]
    · simp
  have hv : ∀ j, v (v⁻¹ j) = j := fun j => by simp
  intro i j hij
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) R) j (v⁻¹ j)) := by
    have h := key (v⁻¹ j) (v⁻¹ j)
    rw [hv, if_pos rfl] at h
    exact IsUnit.of_mul_eq_one_right _ h
  have h := key i (v⁻¹ j)
  rw [hv, if_neg hij] at h
  exact hu.mul_left_eq_zero.1 h

end WeylCell

end GlobalTheory

end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.liftObj_sq | exact GlobalTheory.SqLift.liftObj_sq | (intros; apply GlobalTheory.SqLift.liftObj_sq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.Hom.liftHom_sq | exact GlobalTheory.SqLift.Hom.liftHom_sq | (intros; apply GlobalTheory.SqLift.Hom.liftHom_sq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_heckeCharacter_of_unitary_tensorIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  first | exact @GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | exact GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | (intros; apply GlobalTheory.HeckeTensorRead.exists_hchar_chrEq <;> assumption)
end
