module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundlePointCarryingOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem spMap_comp_spMap_cell {R R' U : Type} [CommRing R] [CommRing R'] [CommRing U] (f : R →+* R')
    (f' : R' →+* U) : spMap f' ≫ spMap f = spMap (f'.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom f')).symm

theorem base_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp MvPolynomial.C) ≫ tau (A.aff k.1) := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap_cell]
  rfl

theorem le_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V := by
  rw [← hx, base_cellPt hZ k z hz]
  exact le_preimage_comp _ (tau_le (A.aff k.1) le_rfl)

theorem g_cellPt (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hV : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V)
    (en : En Dw.mult) :
    ∃ hu, z ≫ g en = pt (str x) (plk (fun (t : Let Dw.mult) r =>
      ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from
        (cellFrames hZ ht).uAt k z hz t.1)) r t.2) en.2.1) hu := by
  have hb := base_cellPt hZ k z hz
  set φ := (ev z _ hz).comp (cellθ κ k).toRingHom with hφ
  have hev : ev x _ hV = φ.comp MvPolynomial.C := by
    subst hx
    rw [ev_congr hb _ hV (hb ▸ hV)]
    exact ev_spMap_tau _ _ _
  have hstr : str x = (φ.comp MvPolynomial.C).comp (A.alpha k.1) := by
    refine LowRank.str_eq ?_
    rw [← hx, hb, Category.assoc, ← spMap_comp_spMap_cell (A.alpha k.1) (φ.comp MvPolynomial.C)]
    congr 1
    exact (spMap_ev_top _).symm
  obtain ⟨hu, e⟩ := hZ.plk.plk k.1 k.2 en
  have key : ∀ (f f' : c.F →+* S) (v v' : Fin (plN A.N en.1 + 1) → S) hv, f = f' → v = v' →
      ∃ hv', pt f v hv = pt f' v' hv' := by
    rintro f _ v _ hv rfl rfl
    exact ⟨hv, rfl⟩
  conv => enter [1, hu']; lhs; rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, e]
  have hspan : Ideal.span (Set.range (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)) = ⊤ := by
    rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (plN A.N en.1 + 1)) c.F) := MvPolynomial.gradedAlgebra
  have hmap : spMap φ ≫ pt (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F)))
      (plk (uvec (A.cv k.1) k.2) en.2.1) hu =
      pt (φ.comp (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F))))
        (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)
        hspan := by
    refine (ProjPoint.SpecMap_ofHom _ _ _ φ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  rw [hmap]
  refine key _ _ _ _ _ (by rw [hstr]; rfl) ?_
  rw [map_plk]
  congr 1
  funext t r
  rw [Function.comp_apply, uvec_cv]
  show φ _ = _
  rw [← Matrix.map_apply (f := φ), Matrix.map_mul, Matrix.map_map, hev]
  rfl

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ z z' x hx hx' hst
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z
  obtain ⟨k', hz'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z'
  have hV := le_cellPt hZ k z hz hx
  have hV' := le_cellPt hZ k' z' hz' hx'
  have hM : ⊤ ≤ x ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    le_preimage_inf ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx')

  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, (cellFrames hZ ht).vecAt k' z' hz' hx' σ i = ∑ j, b j i • (cellFrames hZ ht).vecAt k z hz hx σ j :=
    fun σ => exists_tri_of_eq ((cellFrames hZ ht).linearIndependent_vecAt k z hz hx σ) fun i => by
      rw [← (cellFrames hZ ht).step_eq k z hz hx, ← (cellFrames hZ ht).step_eq k' z' hz' hx', hst]
  choose B hB hBu hBe using ex
  obtain ⟨a, ha⟩ := A.tw S x k'.1 k.1 hV' hV hM

  have hU : ∀ σ, (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev x _ hM) *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k' z' hz' σ) =
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k z hz σ) * B σ := by
    intro σ
    ext r i
    have e := hBe σ i
    rw [(cellFrames hZ ht).sum_vecAt k z hz hx σ (fun j => B σ j i)] at e
    have e2 := vec_chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart x ((cellFrames hZ ht).inM hz hx)
      ((cellFrames hZ ht).inM hz' hx') hM (fun j => (cellFrames hZ ht).uAt k' z' hz' σ j i)
    have e3 := congrFun ((vec _ _ _).injective (e2.trans e)) r
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using e3

  have hc : ∀ (t : Let Dw.mult), (fun r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2) =
      ∑ j, (a * B t.1 j t.2 : S) • fun r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r j := by
    intro t
    funext r
    rw [ha, Matrix.smul_mul, Matrix.mul_assoc, hU t.1, ← Matrix.mul_assoc]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have htri : Tri (fun (t : Let Dw.mult) r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r t.2)
      (fun (t : Let Dw.mult) r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2)
      (fun t => a * B t.1 t.2 t.2) := by
    rintro ⟨σ, i⟩
    have h1 := hc ⟨σ, i⟩
    dsimp only at h1 ⊢
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
    · rw [hB σ (show id i < id j from h), mul_zero, zero_smul]
      exact Submodule.zero_mem _
  refine hZ.ext _ z z' (hx.trans hx'.symm) fun en => ?_
  obtain ⟨hu, e⟩ := g_cellPt hZ ht k z hz hx hV en
  obtain ⟨hu', e'⟩ := g_cellPt hZ ht k' z' hz' hx' hV' en
  rw [e, e']
  have hd : IsUnit (∏ l, a * B (en.2.1 l).1 (en.2.1 l).2 (en.2.1 l).2) :=
    IsUnit.prod_univ_iff.2 fun l => a.isUnit.mul (hBu _ _)
  exact (pt_eq_pt_iff _ hu hu').2 ⟨hd.unit, by rw [plk_tri _ _ S A.N _ _ _ en.1 en.2.1 htri en.2.2]; rfl⟩

end GlobalTheory.FlagMod.FieldFlag
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.exists_flagBundle_point_carrying_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), (∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂) → (∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P') → ∃ z : Sp S ⟶ Z, (cellFrames hZ ht).Lies z P := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local | exact GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetRatio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {σ σ' : Rule t π p q}

theorem sec_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) (a : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (b : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) : σ R' x' v' w' = g (σ R x v w) :=
  hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v' w'
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h' hx a b

theorem ratio_frame (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') {j : c.F →+* R} {x : Sp R ⟶ X} {v w v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w') {a : R}
    (e : σ' R x v w = a * σ R x v w) : σ' R x v' w' = a * σ R x v' w' := by
  have h₁ : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  choose M hM using fun i => (h.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  have ow : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin q) (Fin q) R) i) w (w i) :=
    fun i => DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have ov : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin p) (Fin p) R) i) v' (v' i) :=
    fun i => DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
  have e1 := hσ.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e1' := hσ'.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e2 := hσ.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  have e2' := hσ'.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  rw [Matrix.det_one, _root_.one_mul] at e1 e1' e2 e2'
  have hu : IsUnit (Matrix.of M).det := isUnit_of_mul_isUnit_left (e1 ▸ hn R j x v w h)
  have e3 : σ' R x v' w = a * σ R x v' w := by
    refine hu.mul_left_cancel ?_
    rw [← e1', e, e1]; ring
  rw [← e2', ← e2, e3]; ring

theorem ratio_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) {a : R} (e : σ' R x v w = a * σ R x v w) :
    σ' R' x' v' w' = g a * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h hx
  obtain rfl := (exists_chg g h h' hx).1
  refine ratio_frame hσ hn hσ' h₁ h' ?_
  rw [sec_pull hσ g h h₁ hx a₁ b₁, sec_pull hσ' g h h₁ hx a₁ b₁, e, map_mul]

theorem exists_ratio_affine (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ)
    (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ) (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ')
    {W : X.Opens} (hW : IsAffineOpen W) {j₀ : c.F →+* Γ(X, W)} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v₀ w₀) :
    ∃ f : Γ(X, W), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, ⊤ ≤ x ⁻¹ᵁ W →
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x W f * σ R x v w := by
  obtain ⟨u, hu⟩ := hn _ j₀ _ v₀ w₀ h₀
  refine ⟨σ' _ _ v₀ w₀ * u.inv, fun R _ j x v w hx h => ?_⟩
  rw [Points.valR_eq x W hx]
  refine ratio_pull hσ hn hσ' (Points.valMap x W hx).hom h₀ h (Points.specMap_valMap_fromSpec hW x hx).symm ?_
  rw [← hu, _root_.mul_assoc, u.inv_val, _root_.mul_one]

theorem valR_fromSpec {A : X.Opens} (hA : IsAffineOpen A) (f : Γ(X, A)) :
    valR (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A f = f := by
  have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
  rw [Points.valR_eq _ A hx]
  have : Points.valMap (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A hx = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono hA.fromSpec, Points.specMap_valMap_fromSpec]
    exact ((congrArg (· ≫ hA.fromSpec) (Spec.map_id _)).trans (Category.id_comp _)).symm
  rw [this]
  rfl

end GlobalTheory.DetRatio


open GlobalTheory.DetRatio in
theorem GlobalTheory.detLine_exists_ratio (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ)
    (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q) (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q)
    (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') :
    ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  choose W hW j₀ v₀ w₀ hz h₀ using fun z : V => hc z z.2
  choose f hf using fun z : V => exists_ratio_affine hσ hn hσ' (hW z) (h₀ z)
  have hle : ∀ z, W z ≤ V := fun z y hy => (h₀ z).2.1 (by
    change y ∈ Set.range (hW z).fromSpec
    rw [(hW z).range_fromSpec]; exact hy)
  have hcov : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hz _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W f := by
    intro a b
    refine X.sheaf.eq_of_locally_eq' (fun A : {A : X.affineOpens // A.1 ≤ W a ⊓ W b} => A.1.1) (W a ⊓ W b)
      (fun A => homOfLE A.2) (fun y hy => ?_) _ _ fun A => ?_
    · obtain ⟨_, ⟨A, hA, rfl⟩, hy', hA'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy (W a ⊓ W b).2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨A, hA⟩, hA'⟩, hy'⟩
    · obtain ⟨⟨A, hA⟩, hAle⟩ := A
      replace hA : IsAffineOpen A := hA
      have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
      have hxa := Points.le_preimage_mono _ (hAle.trans inf_le_left) hx
      have hxb := Points.le_preimage_mono _ (hAle.trans inf_le_right) hx
      have hxab := Points.le_preimage_mono _ hAle hx
      obtain ⟨v, w, h, -, -⟩ := exists_pull (Points.valMap _ (W a) hxa).hom (h₀ a)
        (Points.specMap_valMap_fromSpec (hW a) _ hxa).symm
      have e := (hn _ _ _ v w h).mul_right_cancel ((hf a _ _ _ v w hxa h).symm.trans (hf b _ _ _ v w hxb h))
      refine (valR_fromSpec hA _).symm.trans (Eq.trans ?_ (valR_fromSpec hA _))
      refine (Points.valR_res _ hAle hx _).trans (Eq.trans ?_ (Points.valR_res _ hAle hx _).symm)
      exact (Points.valR_res _ inf_le_left hxab _).trans (e.trans (Points.valR_res _ inf_le_right hxab _).symm)
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W V (fun z => homOfLE (hle z)) hcov f hcomp
  refine ⟨F, fun R _ j x v w h => ?_⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => h.2.1 ⟨y, rfl⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let g := algebraMap R (Localization.AtPrime J)
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h rfl
  let z : V := ⟨(spMap g ≫ x) (IsLocalRing.closedPoint (Localization.AtPrime J)), h₁.2.1 ⟨_, rfl⟩⟩
  have hxW : ⊤ ≤ (spMap g ≫ x) ⁻¹ᵁ W z := (Points.le_preimage_iff _ _).2 (hz z)
  have e := hf z _ _ _ v₁ w₁ hxW h₁
  rw [sec_pull hσ g h h₁ rfl a₁ b₁, sec_pull hσ' g h h₁ rfl a₁ b₁, ← hF z] at e
  have e' := (Points.valR_res _ (hle z) hxW F).trans (Points.valR_spMap_comp g x V hxV F)
  change g _ = 0
  rw [map_sub, map_mul, ← e', sub_eq_zero]
  exact e
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.DvrUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] {β' : O' →+* c.F}
  {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ext (Z : Model Xo c β) (U : Set (Xo.XF c)) (j : c.F →+* R) (x : Sp K ⟶ Xo.XF c)
    (h1 : x ≫ toF Xo c = spMap ((algebraMap R K).comp j)) (hU : Set.range x ⊆ U) :
    ∃ χ : Sp R ⟶ gen Z, χ ≫ genStr Z = spMap j ∧ x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ ∧
      Set.range χ ⊆ compactOf Z U := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h2, h3⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap j) (x ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp]
    exact h1)
  refine ⟨χ, h3, h2.symm, ?_⟩
  rintro _ ⟨p, rfl⟩
  let g0 : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hg : χ (spMap (algebraMap R K) g0) ∈ Z.jQ '' U := by
    rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]
    exact ⟨_, hU ⟨g0, rfl⟩, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap R K) g0} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap R K) (⊥ : Ideal K) ≤ (p : PrimeSpectrum R).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hg)


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_ident (Z : Model Xo c β) {χ : Sp R ⟶ gen Z} {x : Sp K ⟶ Xo.XF c}
    (hχ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)) {t : SAB H (Sp R)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap R K))) (mF : SABMap tK Z.oF.t x),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) x
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) x Z.m mF
  have hj : x ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap R K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap R K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_lift_vec {Z : Model Xo c β} {Y : Model Xo c β'} {χ : Sp R ⟶ gen Z} {χ' : Sp R ⟶ gen Y}
    {x : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)} {t t' : SAB H (Sp R)}
    {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Y.t (χ' ≫ genι Y)} {ψ : SABMap t t' (𝟙 (Sp R))}
    {a : SABMap tK t (spMap (algebraMap R K))} {a' : SABMap tK t' (spMap (algebraMap R K))}
    {mF : SABMap tK Z.oF.t x} {mF' : SABMap tK Y.oF.t x}
    (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Y.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Y.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _)
    (w' : epsAt x ⟶ Y.oF.t.G)
    (hw3 : w'.left ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : epsAt x ⟶ Z.oF.t.G, w.left ≫ Z.m0.toSABMap.φ = w'.left ≫ Y.m0.toSABMap.φ ∧
      w.left ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
  rw [Category.comp_id] at hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Sp (DualNumber K) ⟶ Y.oF.t.G.left, w₀ = w'.left := ⟨_, rfl⟩
  have hw1 : w₀ ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := hw₀ ▸ Over.w w'
  have hw3' : w₀ ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ := hw₀ ▸ hw3
  obtain ⟨u, e1, hu1⟩ : ∃ u : Sp (DualNumber K) ⟶ tK.G.left, u ≫ mF'.φ = w₀ ∧
      u ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) :=
    ⟨mF'.cart.1.lift _ _ hw1, mF'.cart.1.lift_fst _ _ _, mF'.cart.1.lift_snd _ _ _⟩
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap R K) =
      spMap (Chart.dualMapR (algebraMap R K)) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp]
    congr 1
    ext z <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : u ≫ a.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3']
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  have k1 : (u ≫ mF.φ) ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := by
    rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  have k2 : (u ≫ mF.φ) ≫ Z.m0.toSABMap.φ = w₀ ≫ Y.m0.toSABMap.φ := by
    rw [Category.assoc, hF0, ← e1, Category.assoc, hF0']
  have k3 : (u ≫ mF.φ) ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
    rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]
  subst hw₀
  exact ⟨Over.homMk (u ≫ mF.φ) k1, k2, k3⟩

theorem exists_move (Y : Model Xo c β') (Z : Model Xo c β) {xR : Sp R ⟶ gen Y} {xZ : Sp R ⟶ gen Z}
    {x : Sp K ⟶ Xo.XF c} (hY : x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR) (hZ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ xZ)
    (χ : 𝓞 E →+* R) {n : ℕ} (vR : Fin n → (epsAt (xR ≫ genι Y) ⟶ Y.t.G))
    (hvR : IsEigBasisAt Y.t.act (xR ≫ genι Y) χ vR) {v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} (hs : SameVecs Y x v vb)
    (hb : ∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) :
    ∃ vZ : Fin n → (epsAt (xZ ≫ genι Z) ⟶ Z.t.G), IsEigBasisAt Z.t.act (xZ ≫ genι Z) χ vZ ∧
      ∀ vK : Fin n → (epsAt ((x ≫ Z.jQ) ≫ genι Z) ⟶ Z.t.G),
        (∀ i, (vK i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vZ i).left) → SameVecs Z x v vK := by
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (x ≫ toX Xo c) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xZ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xR ≫ genι Y) Y.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_ident Z hZ mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_ident Y hY mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map R K t t' tK a a'
  obtain ⟨e, he, hbe⟩ := BdryUnit.exists_eigEquiv m.cart m.act (𝟙 _) (xZ ≫ genι Z) (Category.id_comp _).symm
  obtain ⟨e', he', hbe'⟩ := BdryUnit.exists_eigEquiv m'.cart m'.act (𝟙 _) (xR ≫ genι Y) (Category.id_comp _).symm
  obtain ⟨f, hf, hbf⟩ := BdryUnit.exists_eigEquiv ψ.cart ψ.act (𝟙 _) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : Fin n → _, vR = fun i => e' (f (v₀ i)) :=
    ⟨fun i => f.symm (e'.symm (vR i)), funext fun i => by simp⟩
  refine ⟨fun i => e (v₀ i), (hbe χ n v₀).1 ((hbf χ n v₀).2 ((hbe' χ n fun i => f (v₀ i)).2 hvR)), fun vK hK i => ?_⟩
  obtain ⟨w', h1, h2⟩ := hs i
  have h3 := h2.trans (hb i)
  rw [he', hf] at h3
  obtain ⟨w, h4, h5⟩ := exists_lift_vec hψ hF0 hFm hF0' hFm' (Over.w (v₀ i)) w' h3
  refine ⟨w, h4.trans h1, h5.trans ?_⟩
  rw [hK i, he]

theorem unit_in_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hsec hnz hres R K _ _ _ _ _ _ j xR x V vR wR v w vb wb
    hR hU hx hv hw ev ew
  obtain ⟨xZ, h1, h2, h3⟩ := exists_ext Z U j x hU.1 hU.2.1
  obtain ⟨vZ, hvZ, sv⟩ := exists_move Y Z hx h2 _ vR hR.2.2.1 hv ev
  obtain ⟨wZ, hwZ, sw⟩ := exists_move Y Z hx h2 _ wR hR.2.2.2 hw ew
  have hZ : FrY Z (compactOf Z U) τ j xZ vZ wZ := ⟨h1, h3, hvZ, hwZ⟩
  obtain ⟨vK, wK, hK, a, b⟩ := exists_pull (algebraMap R K) hZ h2
  obtain ⟨u, hu⟩ := hnz R j xZ vZ wZ hZ
  refine ⟨u, ?_⟩
  rw [← hres K _ x v w vK wK hU hK (sv vK a) (sw wK b), hu]
  exact hsec.1 R K (algebraMap R K) (Chart.dualMapR (algebraMap R K)) j _ xZ _ vZ wZ vK wK
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) hZ hK h2 a b

end GlobalTheory.DetLine.DvrUnit
end
end

section


theorem _root_.GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | exact GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | (intros; apply GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare <;> assumption)
end
