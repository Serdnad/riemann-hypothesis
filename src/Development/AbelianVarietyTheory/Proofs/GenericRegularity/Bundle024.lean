module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

section



noncomputable section

namespace GlobalTheory.Reg.TieUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_loc {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ p ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), p ∈ W ∧ resG X hW a = resG X hW b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro p hp
  obtain ⟨W, hW, hpW, e⟩ := h p hp
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) p hpW a
  have e2 := X.presheaf.germ_res_apply (homOfLE hW) p hpW b
  exact e1.symm.trans ((congrArg _ e).trans e2)

theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s
  cases t
  congr 1
  exact funext h

theorem isoMaps_unique {X : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (w : LB.Iso L M) (σ : LB.Sec L)
    {s s' : LB.Sec M} (h : IsoMaps w σ s) (h' : IsoMaps w σ s') : s = s' := by
  refine sec_ext fun i => eq_of_loc _ _ fun p hp => ?_
  obtain ⟨k, hk⟩ := exists_chart hL p
  exact ⟨M.U i ⊓ L.U k, inf_le_left, ⟨hp, hk⟩, (h i k).trans (h' i k).symm⟩

theorem appLE_injective {X Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g] (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (h' : g ⁻¹ᵁ U ≤ V) : Function.Injective (g.appLE U V h).hom := by
  obtain rfl : V = g ⁻¹ᵁ U := le_antisymm h h'
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (g.app U)).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem rigIso_unique {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {g : S' ⟶ S} (m : SABMap t' t g)
    (hab : IsAbelianScheme t'.G) {w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := S') (exists_chart t'.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem lift_abelian (Λ : M.Lift f x) : IsAbelianScheme Λ.t'.G := by
  have hp : IsProper Λ.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) Λ.m1.cart.1 Xo.univ.proper
  exact ⟨Λ.t'.semi.comm, Λ.t'.semi.smooth, hp, Λ.t'.semi.geomConnected⟩

theorem lift_mem (Λ : M.Lift f x) (p : Λ.t'.G.left) : Y.t.G.hom (Λ.m2.φ p) ∈ M.U := by
  have e : Λ.m2.φ ≫ Y.t.G.hom = Λ.t'.G.hom ≫ spMap f ≫ M.hU.fromSpec := Λ.m2.cart.1.w
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have := M.hU.range_fromSpec
  exact this.le ⟨_, rfl⟩

theorem thTie_unique (Λ : M.Lift f x) {s s' : LB.Sec (PPx x)} (h : Λ.ThTie s) (h' : Λ.ThTie s') : s = s' := by
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, b⟩ := h
  obtain ⟨w1', w2', σ', s1', r1', r2', i1', a', b'⟩ := h'
  obtain rfl : w1 = w1' := rigIso_unique Λ.m1 (lift_abelian Λ) r1 r1'
  obtain rfl : w2 = w2' := rigIso_unique Λ.m2 (lift_abelian Λ) r2 r2'
  obtain rfl : σ = σ' := by
    refine sec_ext fun k => eq_of_loc _ _ fun p hp => ?_
    obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Λ.m2.φ p)
    have h₁ : (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k ≤
        Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq => ⟨lift_mem Λ q, mem_pull.1 hq.1⟩
    refine ⟨(Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k, inf_le_right, ⟨mem_pull.2 hj, hp⟩, ?_⟩
    have e := (a j k _ h₁ le_rfl).symm.trans (a' j k _ h₁ le_rfl)
    exact (((w2.s (fun _ => j, k)).isUnit.map _).mul_left_cancel e)
  obtain rfl : s1 = s1' := isoMaps_unique Λ.t'.PP.isLB w1 σ i1 i1'
  have hc : IsPullback Λ.t'.G.hom Λ.m1.φ x Xo.univ.t.G.hom := Λ.m1.cart.1.flip
  let g : Λ.t'.G.left ⟶ Gx x := hc.isoPullback.hom
  have hg : IsIso g := inferInstanceAs (IsIso hc.isoPullback.hom)
  have g1 : g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ := hc.isoPullback_hom_snd
  have g2 : g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom := hc.isoPullback_hom_fst
  refine sec_ext fun i => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Xo.univ.t.PP.L.ι, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k => congrArg i (Subsingleton.elim (α := Fin 1) k 0)⟩
  have hm : ∀ q : Λ.t'.G.left, q ∈ g ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ Λ.m1.φ q ∈ Xo.univ.t.PP.L.U j := by
    intro q
    rw [← g1, Scheme.Hom.comp_apply]
    exact ⟨fun hq => Set.mem_iInter.1 hq (0 : Fin 1), fun hq => Set.mem_iInter.2 fun _ => hq⟩
  have h₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
    fun q hq => (hm q).2 (mem_pull.1 hq)
  exact appLE_injective g _ _ h₁ (fun q hq => mem_pull.2 ((hm q).1 hq))
    ((b g g1 g2 (fun _ => j) h₁).symm.trans (b' g g1 g2 (fun _ => j) h₁))

theorem frPt_eq_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (y z : FrPt Xo c L), M.Comparison₂ f u y → M.Comparison₂ f u z → y.x = z.x → y = z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f u y z hy hz hx
  obtain ⟨x, xo, v, t1, t2, t3, s, t4⟩ := y
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := z
  obtain rfl : x = x' := hx
  obtain ⟨Λ, hv, hs⟩ := hy
  obtain ⟨Λ', hv', hs'⟩ := hz
  obtain ⟨k1, k2⟩ := GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f x Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M L f x Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := thTie_unique Λ hs (k2 _ hs')
  rfl

end GlobalTheory.Reg.TieUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem triangular_inv_of_diag_ne {L : Type} [Field L] {n : ℕ} (b : Matrix (Fin n) (Fin n) L)
    (hb : b.BlockTriangular id) (hd : ∀ i, b i i ≠ 0) :
    b * b⁻¹ = 1 ∧ (b⁻¹).BlockTriangular id ∧ ∀ i, b⁻¹ i i ≠ 0 := by

  have hdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  let _ : Invertible b := Matrix.invertibleOfIsUnitDet b hdet
  have htri : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.mul_nonsing_inv b hdet, htri, fun i => ?_⟩

  have hii : (b⁻¹ * b) i i = b⁻¹ i i * b i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hki with h | h
    · rw [htri h, zero_mul]
    · rw [hb h, mul_zero]
  rw [Matrix.nonsing_inv_mul b hdet, Matrix.one_apply_eq] at hii
  exact left_ne_zero_of_mul_eq_one hii.symm

theorem scal_mul_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a a' : S) (i : (PPx x).ι) :
    scal x (a * a') i = scal x a i * scal x a' i := by
  simp only [scal, map_mul, Out.liftFun]

theorem scal_one_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  simp only [scal, map_one, Out.liftFun]

theorem frBor_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y z : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), z.x = y.x → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → M.Comparison₂ f u z → ∃ t : Ix Dw → Lˣ, FrBor t y z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f y z Λ u b hxz hb hΛ hM
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  subst hxz
  obtain ⟨Λ', hΛ'u, -⟩ := hM

  have hB : ∀ τ, b τ * (b τ)⁻¹ = 1 ∧ ((b τ)⁻¹).BlockTriangular id ∧ ∀ i, (b τ)⁻¹ i i ≠ 0 :=
    fun τ => triangular_inv_of_diag_ne (b τ) (hb τ).1 (hb τ).2

  obtain ⟨a, ha, -⟩ := y.gen zs
  obtain ⟨a', ha', -⟩ := zg y.s
  obtain ⟨w, -, huniq⟩ := zg zs
  have h1 : ∀ i, zs.f i = scal y.x (a * a') i * zs.f i := fun i => by
    rw [scal_mul_tie, _root_.mul_assoc, ← ha' i, ← ha i]
  have h2 : ∀ i, zs.f i = scal y.x 1 i * zs.f i := fun i => by
    rw [scal_one_tie, _root_.one_mul]
  have haa : a * a' = 1 := (huniq _ h1).trans (huniq _ h2).symm
  refine ⟨fun k => Option.elim k (Units.mkOfMulEqOne a a' haa)
    (fun p => Units.mk0 ((b p.1)⁻¹ p.2 p.2) ((hB p.1).2.2 p.2)), ?_⟩
  unfold FrBor
  refine ⟨rfl, fun τ i => ⟨fun j => (b τ)⁻¹ j i, rfl, fun j hij => (hB τ).2.1 hij, ?_⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  ·
    refine (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M L f y.x Λ (Dw.mult τ) (fun j k => (u τ * b τ) k j)
      (y.u τ) (fun j => (b τ)⁻¹ j i) (zu τ i) (fun j => hΛ τ j)).mpr ?_
    have hv := (GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f y.x Λ' Λ).1 _ _ (hΛ'u τ i)
    convert hv using 1
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (b τ)⁻¹ j i * (u τ * b τ) k j = (u τ * b τ * (b τ)⁻¹) k i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
      _ = u τ k i := by rw [Matrix.mul_assoc, (hB τ).1, Matrix.mul_one]
  ·
    have e : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, e, Option.elim_none, Units.val_mkOfMulEqOne]
    erw [op_id, CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.hom_id, RingHom.id_apply]
    exact (ha i).symm

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem MChart.tie_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R S : Type) [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] (f : Γ(Y.X, M.U) →+* R) (ψ : R →ₐ[c.F] S) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R) (y : FrPt Xo c R) (z : FrPt Xo c S), M.Comparison₂ f u y → FrMap ψ y z → M.Comparison₂ (ψ.toRingHom.comp f) (fun τ => (u τ).map ψ) z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R S _ _ _ _ f ψ u y z hT hF
  obtain ⟨Λ, hL, hS⟩ := hT
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  have hbase := GlobalTheory.T.lift_baseChange_alt E H Dw l Xo c O β Y M R f y.x Λ S ψ
  obtain ⟨Λ', hV, hTh⟩ := hbase
  rcases z with ⟨zx⟩
  dsimp only at hx hu h1 h2 h3 ⊢
  subst hx
  refine ⟨Λ', fun τ i => ?_, hTh _ _ pm h1 h2 h3 hS⟩
  have hv := hV _ _ (hL τ i)
  rw [← hu τ i] at hv
  exact hv

end GlobalTheory.Reg
end

section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_integralGenerator_chartPoint_noInvert : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie_free | exact GlobalTheory.Reg.exists_generator_of_thTie_free | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie_free <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory


open IntegralCusp in
theorem cusp_of_integral_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  intro E _ _ _ H Dw l Xo c hT r U hU a n N w hD hw k m cf hk hcf g hg heq
  unfold Formalism.L2.PjFree.cusp
  refine ⟨hg, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  intro σ hσ
  unfold Formalism.L2.PjFree.holSub
  refine Submodule.subset_span ?_
  show Formalism.L2.PjFree.IsHolCusp _ _ _
  unfold Formalism.L2.PjFree.IsHolCusp
  intro j
  have hDk : Dom (k • a) (k * n) := by
    unfold Dom at hD ⊢
    refine ⟨fun τ i i' hii' => ?_, hD.2.mul_left k⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_left k (hD.1 τ hii')
  have hla : Formalism.L2.PjFree.laU (U σ) (k • a) (k * n) j = k • Formalism.L2.PjFree.laU (U σ) a n j := by
    funext τ i
    rw [laU_nsmul (U σ) a n k hD.2 j τ i]
    simp [Pi.smul_apply]
  have hsec := (hU σ hσ).2.2.2.2.1 (k • a) (k * n) hDk g hg j
  rw [hla] at hsec ⊢
  have hwS : ∀ s, Formalism.L2.PjFree.rdU (U σ) (w s) j ∈ ((U σ).X j).SS (Formalism.L2.PjFree.laU (U σ) a n j) := by
    intro s
    have h1 := hw s
    unfold Formalism.L2.PjFree.cusp at h1
    have h2 := h1.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (h2 σ hσ) j
  refine cuspForm_of_integral_over_cuspForms E r ((U σ).X j) (Formalism.L2.PjFree.laU (U σ) a n j) N k m
    (fun s => Formalism.L2.PjFree.rdU (U σ) (w s) j) (fun i => MvPolynomial.map σ (cf i))
    (Formalism.L2.PjFree.rdU (U σ) g j) hwS hk (fun i hi => (hcf i hi).map σ) hsec ?_
  intro x hx
  have : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hy := hT (CAt σ) ((U σ).un j ⟨x, hx⟩)
  have key : ∀ f, Formalism.L2.PjFree.rdU (U σ) f j x = evHom ((U σ).un j ⟨x, hx⟩) hy f := by
    intro f
    unfold Formalism.L2.PjFree.rdU
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
    rfl
  simp only [key]
  have h3 := congrArg (evHom ((U σ).un j ⟨x, hx⟩) hy) heq
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_add (f := _), map_mul, map_sum, map_pow, map_zero, evHom_aeval] using h3

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem mulVec_single_of_support {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (h : Matrix (Fin g) (Fin g) ℂ) (hs : ∀ j j', h j j' ≠ 0 → (e j).1 = (e j').1) (τ : T) (i : Fin (m τ)) :
    h *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      ∑ i', h (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) := by
  classical
  ext j
  obtain ⟨⟨τ', a⟩, rfl⟩ := e.symm.surjective j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single a (fun b _ hb => ?_) (by simp), Pi.single_eq_same, mul_one]
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hh
    exact hb (eq_of_heq (Sigma.mk.inj (e.symm.injective hh)).2).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · by_contra hne
      have := hs _ _ hne
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact hτ this
    · rw [Pi.single_eq_of_ne, mul_zero]
      intro hh
      exact hτ (Sigma.mk.inj (e.symm.injective hh)).1



theorem frBor_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  intro E _ _ _ H Dw l Xo c σ g e F k P P₀ h₀ y y₀ hP hP₀ hh hs hy hy₀ hu hu₀
  classical
  obtain ⟨hdet, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P₀
    (LinearEquiv.refl _ _) h₀ hP hP₀ (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hh
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hdiag : ∀ j, h₀ j j ≠ 0 := by
    rw [GlobalTheory.PerBor.det_of_support (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) hinj h₀ hs] at hdet
    exact fun j => Finset.prod_ne_zero_iff.1 hdet.ne_zero j (Finset.mem_univ j)
  have hx : y.x = y₀.x := hy.trans (hpt.trans hy₀.symm)
  let cf : ∀ τ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → CAt σ := fun τ i i' =>
    (h₀ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ)
  have hc : ∀ τ i, IsCombAt y₀.x (y₀.u τ) (cf τ i) (y.u τ i) := by
    intro τ i
    have d1 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P₀ (Matrix.mulVecLin h₀) hP₀ hex
      _ _).1 (hu τ i)
    rw [Matrix.mulVecLin_apply, mulVec_single_of_support e h₀ (fun j j' h => (hs j j' h).1)] at d1
    have d2 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P₀ hP₀ _ (y₀.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu₀ τ) _ (y.u τ i)).2 d1
    rw [hy₀]
    exact d2
  obtain ⟨t, ht⟩ := (frBor_calculus E H Dw l Xo c (CAt σ) y₀ y y).2.1 hx fun τ i =>
    ⟨cf τ i, isUnit_iff_ne_zero.2 (hdiag _), fun j hj => by
      by_contra hne
      have := (hs _ _ hne).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact absurd hj (not_lt.2 this), hc τ i⟩
  refine ⟨t, ht, fun j => ?_⟩
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, ha, -, hac⟩ := ht.2.1 τ i
  have htan : IsTanAt y₀.x (y.u τ i) := by rw [← hx]; exact y.tan τ i
  have := (y₀.basis τ (y.u τ i) htan (y.eig τ i)).unique hac (hc τ i)
  rw [← ha, this]
  rfl

end GlobalTheory.FrameNorm
end
