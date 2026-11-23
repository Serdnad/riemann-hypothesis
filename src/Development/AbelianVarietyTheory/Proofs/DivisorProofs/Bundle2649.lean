module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_gen_of_top {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j₀ : K → M.ι) (all : ∀ w : Y, w ∈ LB.wchart M φ j₀) (v : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v := by
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j w hw => ⟨hw, all w⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀) * res (le_top : LB.wchart M φ j ≤ ⊤) v⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v :=
    fun Z r z j h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z (le j) h _).trans (gm_linComb M φ ε r z j j₀ h (all _))) (gm_res r z le_top h _))
  refine ⟨t, fun j j' => Geo.Tor.unit_ext fun w hw => ?_, key⟩
  have hm : (𝟙 Y : Y ⟶ Y) w ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hw
  refine ((gm_res _ w _ hm _).trans (key _ _ w j hm.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) w j j' hm.1 hm.2)
      ((gm_res _ w _ hm _).trans (key _ _ w j' hm.2)))).symm)
  rw [← trF_trans hM φ ε (𝟙 Y) w hm.1 hm.2 (all _), _root_.mul_assoc]
  rfl

theorem jK_app_toOpen {R : Type} [CommRing R] [IsDomain R] (r : R) :
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem exists_isUnitPart : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ y, ∃ n ψ₀, IsUnitPart Q t gam y n ψ₀ := by
  intro R _ _ Q m t gam h y
  obtain ⟨u, n, hn, hc⟩ := h y
  have h0 : ∏ i, t i ^ n i ≠ 0 := right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord hc)
  have h1 : algebraMap R (FractionRing R) (∏ i, t i ^ n i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0
  obtain ⟨j₀, hj, hle, e⟩ := hc
  have all : ∀ w, w ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c y).left) j₀ := fun w =>
    Set.mem_iInter.2 fun _ => hj trivial
  obtain ⟨ψ₀, hg, hv⟩ := exists_gen_of_top Q.P.isLB (K := PUnit) (fun _ => (Q.c y).left) (fun _ => -1) j₀ all (unitOn u)
  refine ⟨n, ψ₀, hg, hn, Units.mk0 _ h1, rfl, fun z J hJ => ?_⟩
  have m₀ : (𝟙 (TK R).left : _ ⟶ _) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀ := hle trivial
  have a := gen_trans (Q.psi_gen y) (𝟙 (TK R).left) z (hJ.mem (fun _ : PUnit => Q.xK y) (𝟙 _)) m₀
  have b := hv _ (toUnit (TK R)).left z _ (hJ.mem (fun _ : PUnit => (Q.c y).left) (toUnit (TK R)).left)
  have c : gm (𝟙 (TK R).left) z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀) ((Q.psi y).s j₀) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (Units.mk0 _ h1)) * gm (toUnit (TK R)).left z ⊤ (unitOn u) := by
    have d : res hle ((Q.psi y).s j₀) =
        unitOn (Units.mk0 _ h1) * (show Γ(Sp (FractionRing R), ⊤)ˣ from pullU (jK R) ⊤ (unitOn u)) := by
      refine Units.ext (e.symm.trans ?_)
      rw [jK_app_toOpen, map_mul, _root_.mul_comm, map_mul]
      refine congrArg₂ (· * ·) rfl ?_
      rw [← jK_app_toOpen]
      exact congrArg _ (by simp [DegPre.toOpen, unitOn])
    refine (gm_res _ z hle trivial _).symm.trans ((congrArg _ d).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))
    exact gm_pull (𝟙 _) (jK R) z ⊤ trivial _
  refine a.trans (Eq.trans ?_ (congrArg _ b).symm)
  rw [c, mul_left_comm]
  rfl

end GlobalTheory.UnitPart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_open_compactOf_isIntegral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  intro E _ _ _ H D l Xo c O _ β Y U hn _ hU
  have hint := isIntegral_open_of_geometricallyConnected E H D l Xo c U hU
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have := Y.jQ_open
  have hop : IsOpen (compactOf Y U) := GlobalTheory.FlatRow.isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (compactOf Y U) :=
    (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  let V : (gen Y).Opens := ⟨compactOf Y U, hop⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  exact ⟨V, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end GlobalTheory.DetLine
end

section

open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem qW_polar_eq_sum_add_transpose {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hβ : ∀ a b, β a b = β b a) (y z : Fin s → X) :
    qW W β (y + z) - qW W β y - qW W β z = ∑ u, ∑ v, (W + W.transpose) u v * β (y u) (z v) := by
  have h : ∑ u, ∑ v, W u v * β (z u) (y v) = ∑ u, ∑ v, W v u * β (y u) (z v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hβ]
  simp only [qW, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, h]
  ring

theorem eq_adjoint_apply_of_qW_polar (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : PosW W) (X₀ : Type) [AddCommGroup X₀]
    (β : LinearMap.BilinForm ℤ X₀) (hβ : ∀ a b, β a b = β b a) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (E E' : Matrix (Fin 8) (Fin 8) ℤ) (hE : (W + W.transpose) * E' = E.transpose * (W + W.transpose))
    (z z' : Fin 8 → X₀)
    (h : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z =
      qW W β (y + z') - qW W β y - qW W β z') :
    z' = fun a => ∑ b, E' a b • z b := by
  simp only [qW_polar_eq_sum_add_transpose W β hβ] at h
  unfold PosW at hW
  set M := W + W.transpose with hM
  have hdet : M.det ≠ 0 := by
    have h1 := hW.det_pos
    have h2 : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
      rw [Int.cast_det]
    rw [h2] at h1
    intro h0
    simp [h0] at h1
  have key : ∀ x : X₀, (fun v => β x (z' v)) = E' *ᵥ (fun v => β x (z v)) := by
    intro x
    rw [← sub_eq_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, sub_eq_zero]
    funext w
    have h1 := h (Pi.single w x)
    have h2 : ∀ a, ∑ b, E a b • (Pi.single w x : Fin 8 → X₀) b = E a w • x := by
      intro a
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    have h3 : ∑ u, ∑ v, M u v * β ((Pi.single w x : Fin 8 → X₀) u) (z' v) = ∑ v, M w v * β x (z' v) := by
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    simp only [h2, h3, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  funext a
  rw [← sub_eq_zero]
  by_contra hne
  have h1 := hpos _ hne
  generalize hd : z' a - ∑ b, E' a b • z b = d at h1
  have h2 := congrFun (key d) a
  have h3 : β d d = 0 := by
    conv_lhs => rw [show β d d = β d (z' a - ∑ b, E' a b • z b) by rw [hd]]

    simp only [map_sub, map_sum, map_zsmul, smul_eq_mul, h2, Matrix.mulVec, dotProduct, sub_self]
  omega

end GlobalTheory.Poinc
end

section

open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

open Matrix in
private lemma exists_nat_mul_rat_eq_int' {s : ℕ} (q : Fin s → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin s → ℤ, ∀ u, (N : ℚ) * q u = n u := by
  refine ⟨∏ v, (q v).den, Finset.prod_pos fun v _ => (q v).den_pos,
    fun u => (q u).num * ∏ v ∈ Finset.univ.erase u, ((q v).den : ℤ), fun u => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun v => (q v).den) (Finset.mem_univ u)]
  push_cast
  rw [← Rat.mul_den_eq_num (q u)]
  ring

open Matrix in
private lemma bilinForm_sum_zsmul_eq_sum_mul {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) (n : Fin s → ℤ) :
    β (∑ u, n u • y u) (∑ v, n v • y v) = ∑ u, ∑ v, n u * n v * β (y u) (y v) := by

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
  Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

open Matrix in
private lemma gram_quadratic_real_nonneg {s : ℕ} {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, 0 ≤ β x x) (y : Fin s → X) (c : Fin s → ℝ) :
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ) := by
  have hdense : DenseRange (Pi.map fun _ : Fin s => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on (p := fun c : Fin s → ℝ =>
    0 ≤ ∑ u, ∑ v, c u * c v * ((β (y u) (y v) : ℤ) : ℝ)) c
    (isClosed_le continuous_const (by fun_prop)) fun q => ?_
  obtain ⟨N, hN, n, hn⟩ := exists_nat_mul_rat_eq_int' q
  have hnR : ∀ u, (N : ℝ) * (q u : ℝ) = (n u : ℝ) := fun u => by exact_mod_cast hn u
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (q v : ℝ) * ((β (y u) (y v) : ℤ) : ℝ) =
      ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    rw [bilinForm_sum_zsmul_eq_sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hnR u, ← hnR v]
    ring
  have h0 : (0 : ℝ) ≤ ((β (∑ u, n u • y u) (∑ v, n v • y v) : ℤ) : ℝ) := by
    exact_mod_cast hpos _
  rw [← key] at h0
  exact (mul_nonneg_iff_of_pos_left hNpos).mp h0


open Matrix in
theorem _root_.GlobalTheory.Poinc.qW_nonneg_of_posW : ∀ {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ),
    _root_.GlobalTheory.Poinc.PosW W → ∀ {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ x, 0 ≤ β x x) →
    ∀ y : Fin s → X, 0 ≤ _root_.GlobalTheory.Poinc.qW W β y := by
  intro s W hW X _ β hsymm hpos y
  unfold _root_.GlobalTheory.Poinc.PosW at hW
  unfold _root_.GlobalTheory.Poinc.qW
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW.posSemidef
  set S : ℤ := ∑ u, ∑ w, W u w * β (y u) (y w) with hS
  have hswap : ∑ u, ∑ w, W w u * β (y u) (y w) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [hsymm]
  have htwo : ((2 * S : ℤ) : ℝ) = ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    have : (2 * S : ℤ) = ∑ u, ∑ w, (W u w + W w u) * β (y u) (y w) := by
      simp only [add_mul, Finset.sum_add_distrib, hswap, hS]
      ring
    rw [this]
    push_cast
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hnonneg : (0 : ℝ) ≤ ∑ u, ∑ w,
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)) u w * ((β (y u) (y w) : ℤ) : ℝ) := by
    rw [hv]
    have e : ∀ u w, (∑ i, vecMulVec (v i) (star (v i))) u w * ((β (y u) (y w) : ℤ) : ℝ) =
        ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := by
      intro u w
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_mul]
    simp_rw [e]
    calc (0 : ℝ) ≤ ∑ i, ∑ u, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_nonneg fun i _ => gram_quadratic_real_nonneg β hpos y (v i)
      _ = ∑ u, ∑ i, ∑ w, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) := Finset.sum_comm
      _ = ∑ u, ∑ w, ∑ i, v i u * v i w * ((β (y u) (y w) : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [← htwo] at hnonneg
  have : (0 : ℝ) ≤ (S : ℝ) := by push_cast at hnonneg; linarith
  exact_mod_cast this

end GlobalTheory.Poinc
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Span

lemma dvd_apply_of_coord {r : ℕ} (N : ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (d z : Fin r → ℤ)
    (hd : ∀ i, N ∣ d i) : N ∣ b d z := by
  choose ν hν using hd
  have : d = N • ν := by funext i; simp [hν i]
  rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

lemma qW_dvd {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0)
    (y : Fin s → Fin r → ℤ) : (N : ℤ) ∣ qW W b y := by
  set c : Fin s → Fin r → ZMod N := fun u i => (y u i : ZMod N)
  have hd : ∀ u i, (N : ℤ) ∣ y u i - μ c u i := by
    intro u i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hμ]; simp [c]
  have key : qW W b y = qW W b y - qW W b (μ c) := by rw [h0]; ring
  rw [key, qW, qW, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun v _ => ?_
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ _
  have e : b (y u) (y v) - b (μ c u) (μ c v) = b (y u - μ c u) (y v) + b (y v - μ c v) (μ c u) := by
    rw [hb (y v - μ c v) (μ c u)]
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [e]
  exact dvd_add (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd u i)
    (dvd_apply_of_coord _ b _ _ fun i => by simpa using hd v i)

lemma dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hb : ∀ x y, b x y = b y x) (h0 : ∀ c, qW W b (μ c) = 0) :
    ∀ x z, (N : ℤ) ∣ b x z := by
  obtain ⟨ε, hε⟩ := hε
  set q := ∑ u, ∑ v, W u v * ε u * ε v with hq
  have hcop : IsCoprime (N : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_left_right hε
    simpa [Int.gcd] using this
  have h2 : IsCoprime (N : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.coprime_mul_right_right hε
    simpa [Int.gcd] using this
  have hxx : ∀ x, (N : ℤ) ∣ b x x := by
    intro x
    have h := qW_dvd W N μ hμ b hb h0 (fun u => ε u • x)
    have e : qW W b (fun u => ε u • x) = q * b x x := by
      simp only [qW, map_smul, LinearMap.smul_apply, smul_eq_mul, hq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [e] at h
    exact hcop.dvd_of_dvd_mul_left h
  intro x z
  have e : 2 * b x z = b (x + z) (x + z) - b x x - b z z := by
    simp only [map_add (f := _), LinearMap.add_apply, hb z x]
    ring
  have h : (N : ℤ) ∣ 2 * b x z := by
    rw [e]; exact dvd_sub (dvd_sub (hxx _) (hxx x)) (hxx z)
  exact h2.dvd_of_dvd_mul_left h

end GlobalTheory.Poinc.Span

namespace GlobalTheory.Poinc.Span

lemma pow_dvd_all {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N : ℕ) [NeZero N]
    (hε : ∃ ε : Fin s → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs))
    (μ : (Fin s → Fin r → ZMod N) → (Fin s → Fin r → ℤ)) (hμ : ∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i)
    (k : ℕ) : ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) →
      ∀ x z, (N : ℤ) ^ k ∣ b x z := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro b hb h0 x z
    have hd := dvd_all W N hε μ hμ b hb h0
    let b' : LinearMap.BilinForm ℤ (Fin r → ℤ) := LinearMap.mk₂ ℤ (fun x z => b x z / N)
      (fun m₁ m₂ n => by simp only [map_add (f := _), LinearMap.add_apply, Int.add_ediv_of_dvd_left (hd m₁ n)])
      (fun c m n => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
      (fun m n₁ n₂ => by simp only [map_add (f := _), Int.add_ediv_of_dvd_left (hd m n₁)])
      (fun c m n => by simp only [map_smul, smul_eq_mul, Int.mul_ediv_assoc c (hd m n)])
    have hbb : ∀ x z, b x z = N * b' x z := fun x z => by
      simp only [b', LinearMap.mk₂_apply]; exact (Int.mul_ediv_cancel' (hd x z)).symm
    have hb' : ∀ x z, b' x z = b' z x := fun x z => by simp only [b', LinearMap.mk₂_apply, hb x z]
    have h0' : ∀ c, qW W b' (μ c) = 0 := by
      intro c
      have e : qW W b (μ c) = N * qW W b' (μ c) := by
        simp only [qW, hbb, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      have := h0 c
      rw [e] at this
      exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast NeZero.ne N)
    rw [hbb, pow_succ, mul_comm ((N : ℤ) ^ k)]
    exact mul_dvd_mul_left _ (ih b' hb' h0' x z)

end GlobalTheory.Poinc.Span

theorem GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts :
    ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ,
      (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) →
      ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) → b = 0 := by
  intro W _ N _ hN r hε μ hμ b hb h0
  refine LinearMap.ext₂ fun x z => ?_
  have h := GlobalTheory.Poinc.Span.pow_dvd_all W N hε μ hμ (b x z).natAbs b hb h0 x z
  simp only [LinearMap.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)
end

section

open GlobalTheory.Poinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
end
