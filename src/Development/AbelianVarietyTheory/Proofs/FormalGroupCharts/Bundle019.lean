module

import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle018
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

@[expose] public section

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X)) (ε : K → ℤ)
    (H : LBIso L (LB.LinComb L φ ε)) :
    ∃ t : LB.Gen (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim φ (fun _ => 𝟙 X)) (Sum.elim ε (fun _ => -1))), t.IsGen := by
  obtain ⟨v, hv⟩ := H
  have le : ∀ j : K ⊕ PUnit → L.ι, LB.wchart L (Sum.elim φ (fun _ : PUnit => 𝟙 X)) j ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ L.U (j (Sum.inr PUnit.unit)) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.1 hy (Sum.inr PUnit.unit)⟩
  refine ⟨⟨fun j => res (le j) (v.s (j ∘ Sum.inl, j (Sum.inr PUnit.unit)))⟩,
    fun (p q : K ⊕ PUnit → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit))) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit)))))
    (hv (p ∘ Sum.inl, p (Sum.inr PUnit.unit)) (q ∘ Sum.inl, q (Sum.inr PUnit.unit)))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L (LB.LinComb L φ ε) (𝟙 X) y (p ∘ Sum.inl, p (Sum.inr PUnit.unit))
      (q ∘ Sum.inl, q (Sum.inr PUnit.unit)) hm).trans (congrArg₂ (· * ·)
        (gm_linComb L φ ε (𝟙 X) y _ _ hm.1.1 hm.2.1) rfl)) (gm_res _ y _ hm _))))
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le q) hy.2 _)))
  exact DVR.prod_sum₂ (K := K) (K' := PUnit) _ rfl ((Fintype.prod_unique _).trans (zpow_neg_one _))

theorem gen_ext_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t.s = t'.s := by
  funext j
  exact Units.ext (sec_ext_val hL (s := genSec t ht) (s' := genSec t' ht') (fun y J hJ => by
    rw [sval_genSec t ht _ y hJ, sval_genSec t' ht' _ y hJ, h y J hJ]) j)

theorem prod_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  apply GlobalTheory.NormRos.prod_square <;> assumption

theorem prod_prim {S : Scheme.{0}} {G T : Over S} [GrpObj G] (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ i, h (x.left ≫ primφ w i) ^ primε i =
      h x.left * (h (x * (x ≫ w)).left)⁻¹ * h x.left * h (x ≫ w).left * (h (1 : T ⟶ G).left)⁻¹ := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  rw [Fin.prod_univ_five]
  show h (x.left ≫ 𝟙 _) ^ (1 : ℤ) * h (x ≫ (𝟙 G * w)).left ^ (-1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (1 : ℤ) *
    h (x ≫ w).left ^ (1 : ℤ) * h (x ≫ (1 : G ⟶ G)).left ^ (-1 : ℤ) = _
  rw [e₁, e₄, Category.comp_id]
  simp only [zpow_neg, zpow_one]

theorem exists_unique_normPrim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (w : G ⟶ G) [IsMonHom w],
    LBIso Lr.L (cubeLB G ![𝟙 G, w] Lr.L) →
    (∃ ρ : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig) ∧
    (Function.Surjective G.hom.appTop.hom → ∀ ρ ρ' : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen → ρ'.IsGen →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ' (eSec G)) Lr.rig → ρ.s = ρ'.s) := by
  intro S G _ _ Lr w _ H
  have he : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨?_, fun hp ρ ρ' h h' c c' => gen_ext_val Lr.isLB h h' fun y J hJ =>
    gen_unique Lr.isLB G.hom (eSec G) he hp h h' (fun y J hJ => ?_) _ _ y J hJ⟩
  · obtain ⟨t₀, ht₀⟩ := exists_gen_of_lbIso Lr.L _ _ H
    have P : ∀ (V : Type) [CommGroup V] (k : (G.left ⟶ G.left) → V), ∏ i, k (primφ w i) ^ primε i =
        k (𝟙 _) * (k (𝟙 G * w : G ⟶ G).left)⁻¹ * k (𝟙 _) * k w.left * (k (1 : G ⟶ G).left)⁻¹ := fun V _ k => by
      have := prod_prim w (𝟙 G) k
      simpa only [Over.id_left, Category.id_comp] using this
    obtain ⟨t, ht, -⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K' := PUnit) (U := V) _ (prod_lam (𝟙 G) w k)
        (c' := (k (𝟙 _))⁻¹) (by simp))).trans ?_
      rw [P]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, Over.id_left]
      abel) _ (DVR.invGen_isGen _ _ _ _ ht₀)
    have n : G.hom ≫ eSec G = (1 : G ⟶ G).left := rfl
    obtain ⟨ρ, hρ, hv⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      have p := prod_prim w (1 : G ⟶ G) k
      rw [MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ PUnit) (U := V) _
        (c := ∏ i, k (primφ w i) ^ primε i) rfl
        (DVR.prod_sum₂ (K := Fin 5) (K' := PUnit) (U := V) _ (DVR.prod_neg _ _ p) (c' := k (1 : G ⟶ G).left)
          (by rw [Fintype.prod_unique]; exact zpow_one _))) ?_
      simp)
      (LB.mulGen Lr.L _ _ _ _ t (LB.mulGen Lr.L _ _ _ _
        (LB.invGen Lr.L _ _ (LB.pullGen Lr.L _ _ t (1 : G ⟶ G).left)) (LB.pullGen Lr.L _ _ Lr.rig G.hom)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (DVR.pullGen_isGen _ _ _ _ Lr.rigGen _)))
    refine ⟨ρ, hρ, corr_of_val Lr.isLB fun y J hJ => ?_⟩
    have e₁ : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      rw [← n, ← Category.assoc, he]; exact Category.id_comp _
    rw [val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, e₁,
      mul_inv_cancel_left]
    exact congrArg (fun q => val Lr.rig q y J) he
  · have a := val_corr hJ c (𝟙 _)
    have b := val_corr hJ c' (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

end GlobalTheory.JetSer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartJLaw

variable {T : Type} [CommRing T] {d : ℕ}

theorem psJet_eq_toJet {n : ℕ} (m : ℕ) (f : PS T n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    psJet m f = JetSer.toJet m f := by
  symm
  refine (JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_
  rw [MvPowerSeries.coeff_trunc]
  split_ifs with hlt
  · rfl
  · have hle : e ≤ Finsupp.equivFunOnFinite.symm fun _ => m + 1 := fun i => by
      have := Finsupp.le_degree i e
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
    have heq : e = Finsupp.equivFunOnFinite.symm fun _ => m + 1 := by
      by_contra h
      exact hlt (lt_of_le_of_ne hle h)
    have h0 : e = 0 := by
      ext i
      exfalso
      have h1 := Finsupp.le_degree i e
      have h2 : e i = m + 1 := by rw [heq]; simp
      omega
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

theorem substJ_zR {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (q : Fin 1 × Fin d) : substJ m φ hφ (zR m q) = JetSer.toJet m (φ q.2) := by
  rw [← psJet_eq_toJet m _ (hφ q.2)]
  show MvPolynomial.aeval (fun q : Fin 1 × Fin d => psJet m (φ q.2)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_ev {k n : ℕ} (a : Fin k → Pt T n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS T k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h1) h1 hf

theorem read_pt {G : Over (Sp T)} {A B C D : Type} [CommRing A] [Algebra T A] [CommRing B] [Algebra T B]
    [CommRing C] [Algebra T C] [CommRing D] [Algebra T D] (x : algOver T A ⟶ G) (x0 : Chart.sp (R₀ := T) B ⟶ G)
    (ρ : A →ₐ[T] B) (h : x0.left = spMap (ρ : A →+* B) ≫ x.left) (S : A →ₐ[T] C) (Φ : C →ₐ[T] D) (ψ : B →ₐ[T] D)
    (hψ : ψ.comp ρ = Φ.comp S) :
    (Chart.spMap ψ ≫ x0 : Chart.sp (R₀ := T) D ⟶ G) = algOverHom Φ ≫ algOverHom S ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, h, Chart.spMap_left, algOverHom, Over.homMk_left, ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg (fun f : A →ₐ[T] D => (f : A →+* D)) hψ

theorem isLawOf_of_isChartJ : ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 → (∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left) → GlobalTheory.JetSer.IsLawOf x0 F.F := by
  intro T _ G _ _ d F x hx x0 _ ⟨ρ, hρ1, hρ2⟩
  refine ⟨F.const, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt T n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  have hF : ∀ j, MvPowerSeries.constantCoeff (addOf F.F a b j) = 0 :=
    fun j => constantCoeff_ev _ hab _ (F.const j)
  refine ⟨hF, fun m => ?_⟩
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg T (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d)
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt T n d) p.1 p.2) (fun p => hab p.1 p.2) m
  obtain ⟨ψ, hψ⟩ := JetSer.exists_jetHom (addOf F.F a b) hF m
  have key : ∀ (i : Fin 2) (χ : Chart.JetR T (Fin d) m →ₐ[T] Chart.JetR T (Fin n × Fin d) m),
      (∀ j, χ (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt T n d) i j)) →
      χ.comp (ρ m) = Φ.comp (jetPt (d := d) i m) := by
    intro i χ hχ
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hχ, jetPt, substJ_zR, JetSer.toJet_X, hΦ]
  have keyF : ψ.comp (ρ m) = Φ.comp (substJ m F.F F.const) := by
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hψ, substJ_zR, hsub Φ hΦ]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  show y m * z m = _
  rw [read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψ keyF, hx.law m, MonObj.comp_mul, ha2, hb2,
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψa (key 0 ψa ha1),
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψb (key 1 ψb hb1)]

end GlobalTheory.ChartJLaw
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isUniversalChart_of_formalGroupChart : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  first | exact @GlobalTheory.ChartUniv.isUnivChart_of_isChartJ | exact GlobalTheory.ChartUniv.isUnivChart_of_isChartJ | (intros; apply GlobalTheory.ChartUniv.isUnivChart_of_isChartJ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.frame_symmetry_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (sy : PS S 2 d), (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) ↔ (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (e' m) (scaleGenG t' _ _ (unitΓ u⁻¹) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) := by
  first | exact @GlobalTheory.FrameSym.frame_sym_iff | exact GlobalTheory.FrameSym.frame_sym_iff | (intros; apply GlobalTheory.FrameSym.frame_sym_iff <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TripleFrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  refine Eq.trans ?_ (gm_pull r (spMap f) z ⊤ trivial (unitΓ u))
  refine congrArg (gm r z ⊤) (Units.ext ?_)
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def jetOver (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc

  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetOver ψ x0 d m n =
      jetOver ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  exact congrArg spMap (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetOver ψ x0 d m 1 =
      jetOver ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  have e := PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr (show (fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

variable {ψ x0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (spMap ψ ≫ x0) d m 1 ⟶ t.G}

theorem point_bc (hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap ψ ≫ x0) d x' m i = jetOver ψ x0 d m n ≫ jptG t x0 d x m i := by
  unfold jptG
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (jOG (spMap ψ ≫ x0) d m n).left) :
    val (peG t (spMap ψ ≫ x0) d x' e' m φ') r z J = val (peG t x0 d x e m φ) (r ≫ (jetOver ψ x0 d m n).left) z J := by
  obtain rfl : φ' = fun i j => MvPolynomial.map ψ (φ i j) := funext fun i => funext fun j => hφ i j
  refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
    subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)]

end GlobalTheory.TripleFrameBaseChange

namespace GlobalTheory

open TripleFrameBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X C)

theorem isFrameG_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx0 e e' _ he' hc0 F act ph1 ph2 sy ad h
  subst h01
  have hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m := fun m => Over.OverMorphism.ext (hx0 m)
  have hc : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
      (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left) := hc0
  have hX : ∀ {n : ℕ} (p : Fin n × Fin d), (X p : MvPolynomial (Fin n × Fin d) S') = MvPolynomial.map ψ (X p) :=
    fun p => (MvPolynomial.map_X ψ p).symm
  refine ⟨he', fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hcor⟩ := h.ph1 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph1),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.ph2 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph2),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.sy m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m sy),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_corr hJ (hc m) _).trans ((val_pull hJ _ _ _).trans (k.trans ?_))
    refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
    refine congrArg₂ (· * ·) (gm_unit_map _ u⁻¹ _ y).symm ?_
    exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm
  · obtain ⟨wL, hw, hall⟩ := h.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hcor⟩ := hall m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m (ad a)),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) ((val_mul hJ _ _ _).symm.trans (k.trans ?_)))
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [point_bc hx, point_bc hx, ← comp_lift, Over.comp_left, Category.assoc]
    · exact val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm

end GlobalTheory
end
end
