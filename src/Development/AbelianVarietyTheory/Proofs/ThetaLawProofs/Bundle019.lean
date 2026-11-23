module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Mathlib.RingTheory.FiniteType
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PowSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem sum_mul_cons {T : Type} [CommRing T] {E₂ E : R →+* T} (h₂ : E₂ = E) {n N : ℕ}
    (G : Fin (n + 1) → Fin N → T) (q : Fin N → (Fin n → Fin N) → R) :
    ∑ k, (∑ I, E₂ (q k I) * ∏ d : Fin n, G d.succ (I d)) * G 0 k =
      ∑ I : Fin (n + 1) → Fin N, E (q (I 0) (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Fin.tail_cons]
  ring

theorem span_ev (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (hL : L.IsLB)
    (hb : ∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))),
      ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart L (K := Fin 0) (fun c => (Out.powPr A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    have hF : FormEq (K := Fin (n + 1)) (K' := Fin n ⊕ PUnit) (fun c => (Out.powPr A c).left) (fun _ => t)
        (Sum.elim (fun k => (snd A (Out.powObj A n)).left ≫ (Out.powPr A k).left)
          (fun _ => (fst A (Out.powObj A n)).left))
        (Sum.elim (fun _ => t) (fun _ => t)) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type, mul_comm]
      exact congrArg₂ (· * ·) rfl (Fintype.prod_unique
        (fun _ : PUnit => h (fst A (Out.powObj A n)).left ^ t)).symm
    obtain ⟨v, hv⟩ := exists_sec hL hF s
    obtain ⟨a, ha⟩ := hb (Out.powObj A n) (Fin n) (fun c => (Out.powPr A c).left) (fun _ => t) v
    choose q hq using fun i => ih (a i)
    refine ⟨fun I => q (I 0) (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₂ : (r ≫ (snd A (Out.powObj A n)).left) ≫ (Out.powObj A n).hom =
        r ≫ (Out.powObj A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd A (Out.powObj A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hq i Z _ z J hJ) rfl).trans ?_
    exact sum_mul_cons (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr A d).left) z (L.U (J (r ≫ (Out.powPr A d).left)))
          ((b j).f (J (r ≫ (Out.powPr A d).left)))) q

theorem boxProducts_span_of_boxSpan : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  intro R _ A L t N b hL hb n s
  obtain ⟨q, hq⟩ := span_ev A L t N b hL hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.PowSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.EtaleLocInj

theorem exists_separating_pairs {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (h : φ.Etale) :
    ∃ s : Finset (S × S), ∑ p ∈ s, p.1 * p.2 = 1 ∧ ∀ e e' : S →+* ℂ, e.comp φ = e'.comp φ →
      ∑ p ∈ s, e p.1 * e' p.2 ≠ 0 → e = e' := by
  algebraize [φ]
  obtain ⟨t, ht, h1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := S)).1 inferInstance
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_, fun e e' hee hne => ?_⟩

  · simpa [map_sum] using h1
  · letI : Algebra R ℂ := (e.comp φ).toAlgebra
    let a : S →ₐ[R] ℂ := { e with commutes' := fun _ => rfl }
    let a' : S →ₐ[R] ℂ := { e' with commutes' := fun r => (RingHom.congr_fun hee r).symm }
    let F := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
    ext x
    have h2 := congrArg F (ht x)

    simp only [F, map_mul, map_sub, map_sum, Algebra.TensorProduct.lift_tmul, map_one, map_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have h4 := (sub_eq_zero.1 h3).symm
      rw [_root_.one_mul, _root_.mul_one] at h4
      exact h4
    · exact (hne h3).elim

theorem eq_of_valAtHom_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x x' : Sp ℂ ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valAtHom x U h = valAtHom x' U h') : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h']
  congr 2
  ext1
  exact e

theorem exists_open_injOn :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ), Etale π → IsOpen B → b₀ ∈ B → IsHolTo B y → ∃ B' : Set (Fin m → ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ ∀ b ∈ B', ∀ b' ∈ B', y b ≫ π = y b' ≫ π → y b = y b' := by
  intro X Y π m B y b₀ hπ _ hb₀ hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π (y b₀ (default : PrimeSpectrum ℂ)))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show y b₀ (default : PrimeSpectrum ℂ) ∈ ((π ⁻¹ᵁ V : X.Opens) : Set X) from hxV) (π ⁻¹ᵁ V).isOpen
  have e : U ≤ π ⁻¹ᵁ V := hUV
  obtain ⟨s, hs1, hs⟩ := exists_separating_pairs _ (π.etale_appLE hV hU e)
  set C : Set (Fin m → ℂ) := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} with hC
  have hCo : IsOpen C := (hy U 0).1
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hb₀C : b₀ ∈ C := ⟨hb₀, h₀⟩
  have hc : ∀ f : Γ(X, U), ContinuousAt (fun b => valAt' (y b) U f) b₀ := fun f =>
    (hy U f).2.continuousOn.continuousAt (hCo.mem_nhds hb₀C)
  let F : (Fin m → ℂ) × (Fin m → ℂ) → ℂ := fun q => ∑ p ∈ s, valAt' (y q.1) U p.1 * valAt' (y q.2) U p.2
  have hF : ContinuousAt F (b₀, b₀) := by
    refine tendsto_finsetSum _ fun p _ => ?_
    exact ((hc p.1).comp_of_eq continuousAt_fst rfl).mul ((hc p.2).comp_of_eq continuousAt_snd rfl)
  have hF0 : F (b₀, b₀) ≠ 0 := by
    simp only [F, ← valAt'_mul, ← valAt'_sum, hs1, valAt'_one _ h₀]
    exact one_ne_zero
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hF.eventually_ne hF0)
  obtain ⟨B', hB'sub, hB'o, hB'⟩ := mem_nhds_iff.1
    (Filter.inter_mem (hCo.mem_nhds hb₀C) (Filter.inter_mem hu hv))
  refine ⟨B', hB'o, hB', fun b hb => (hB'sub hb).1.1, fun b hb b' hb' hbb => ?_⟩
  have h1 := (hB'sub hb).1.2
  have h2 := (hB'sub hb').1.2
  refine eq_of_valAtHom_eq hU _ _ h1 h2 (hs _ _ ?_ ?_)
  · ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, ← valAt'_eq_valAtHom, ← valAt'_eq_valAtHom,
      valAt'_appLE _ _ _ _ _ _ h1, valAt'_appLE _ _ _ _ _ _ h2, hbb]
  · simp only [← valAt'_eq_valAtHom]
    have h3 : F (b, b') ≠ 0 := huv (Set.mk_mem_prod (hB'sub hb).2.1 (hB'sub hb').2.2)
    exact h3

end GlobalTheory.EtaleLocInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelOpen

theorem image_mem_nhds_of_injOn {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {a : Fin n → ℂ}
    (ha : a ∈ U) : f '' U ∈ nhds (f a) := by
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn n U f hU hf hinj a ha
  have hm : Filter.map f (nhds a) = nhds (f a) :=
    han.hasStrictFDerivAt.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hb.2)
  rw [← hm]
  exact Filter.image_mem_map (hU.mem_nhds ha)

theorem eq_of_out {J R : Type} {s t : Matrix J J R} (hs : s.IsSymm) (ht : t.IsSymm)
    (h : ∀ z : Sym2 J, s z.out.1 z.out.2 = t z.out.1 z.out.2) : s = t := by
  ext i j
  have h1 := h s(i, j)
  have h2 : s((s(i, j) : Sym2 J).out.1, (s(i, j) : Sym2 J).out.2) = s(i, j) :=
    Quot.out_eq (s(i, j) : Sym2 J)
  rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rwa [h3, h4] at h1
  · rw [h3, h4] at h1
    rw [← hs.apply i j, ← ht.apply i j]
    exact h1

theorem exists_nhds_subset_image :
    ∀ (h : ℕ) (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ) (b₀ : Fin (h * (h + 1) / 2) → ℂ), IsOpen B → b₀ ∈ B → (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → Set.InjOn τ B → ∃ N ∈ nhds (τ b₀), ∀ t ∈ N, t.IsSymm → (t.map Complex.im).PosDef → ∃ b ∈ B, τ b = t := by
  intro h B τ b₀ hB hb₀ hd hs hinj
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (GlobalTheory.card_sym2_fin h)
  let p : Matrix (Fin h) (Fin h) ℂ → (Fin (h * (h + 1) / 2) → ℂ) :=
    fun t k => t (e.symm k).out.1 (e.symm k).out.2
  have hpc : Continuous p := continuous_pi fun k => continuous_id.matrix_elem _ _
  have hp : ∀ s t : Matrix (Fin h) (Fin h) ℂ, s.IsSymm → t.IsSymm → p s = p t → s = t := by
    intro s t hs' ht' hst
    refine eq_of_out hs' ht' fun z => ?_
    have := congrFun hst (e z)
    simpa only [p, Equiv.symm_apply_apply] using this
  have key := image_mem_nhds_of_injOn (f := fun b => p (τ b)) hB
    (differentiableOn_pi.mpr fun k => hd _ _)
    (fun x hx y hy hxy => hinj hx hy (hp _ _ (hs x hx).1 (hs y hy).1 hxy)) hb₀
  refine ⟨_, hpc.continuousAt.preimage_mem_nhds key, ?_⟩
  rintro t ⟨b, hb, hbt⟩ ht -
  exact ⟨b, hb, hp _ _ (hs b hb).1 ht hbt⟩

end GlobalTheory.SiegelOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem _root_.GlobalTheory.KeyTf.exists_finiteType_subring_adjoin :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (F : Finset S), Algebra.FiniteType ℤ R₀ →
      ∃ R₁ : Subring S, R₀ ≤ R₁ ∧ (F : Set S) ⊆ R₁ ∧ Algebra.FiniteType ℤ R₁ := by
  intro S _ R₀ F hR₀
  classical
  obtain ⟨s, hs⟩ := hR₀.out
  let T : Finset S := s.image (Subtype.val) ∪ F
  refine ⟨(Algebra.adjoin ℤ (T : Set S)).toSubring, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : R₀) ∈ Algebra.adjoin ℤ (s : Set R₀) := hs ▸ Algebra.mem_top
    have h2 : x ∈ (Algebra.adjoin ℤ (s : Set R₀)).map R₀.subtype.toIntAlgHom :=
      Subalgebra.mem_map.2 ⟨_, hmem, rfl⟩
    rw [← Algebra.adjoin_image] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨T, rfl⟩

end GlobalTheory.KeyTf
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem eq_of_invariantGen_translates :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (ξ ξ' : 𝟙_ (Over (Sp K)) ⟶ P.A) (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left, ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left] ![1, -1])), (m : K) ≠ 0 → u.IsGen → (∀ δ : 𝟙_ (Over (Sp K)) ⟶ P.A, δ ^ m = 1 → ∀ (y : P.A.left) J, Good P.L y J → val u ((toUnit P.A ≫ δ) * 𝟙 P.A).left y J = val u (𝟙 _) y J) → ξ = ξ' := by
  intro laws K _ _ P m ξ ξ' u hm hu hinv
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hmul : ∀ {Z : Over (Sp K)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A m = y ^ m :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] ![1, -1]
    (Out.mulA P.A m).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ m = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul,
        Out.mulA])
    (fun U f hf => torsion_invariant_descends (fun S _ Q n hn =>
      let ⟨a, b, c, d, _⟩ := laws.mulN S Q n hn; ⟨a, b, c, d⟩) K P m hm U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA]
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA])
    u hu (fun y z J hJ => hinv y.1 y.2 z J hJ)
  let B : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let x : B ⟶ P.A := toUnit B ≫ (ξ * ξ'⁻¹)
  let r : B ⊗ P.A ⟶ P.A := snd B P.A * (toUnit _ ≫ ξ'⁻¹)
  have hx : x = toUnit _ ≫ η[P.A] := by
    refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) =
        ![(lift (fst B P.A ≫ x) (snd B P.A) ≫ μ[P.A]).left, (snd B P.A).left] := by
      funext i
      fin_cases i
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left = ((fst B P.A ≫ x) * snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r, x, comp_toUnit_assoc, MonObj.comp_mul]
        rw [_root_.mul_assoc, _root_.mul_comm (snd B P.A), _root_.mul_comm (toUnit _ ≫ ξ'⁻¹)]
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left = (snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r]
        rw [GrpObj.comp_inv, inv_mul_cancel_right]
    have h4 : ∃ w : LB.Gen (LB.LinComb P.L (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) ![1, -1]),
        w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (Out.translDiff P.A P.L x) w hw _
  let s : 𝟙_ (Over (Sp K)) ⟶ B := Over.homMk (𝟙_ (Over (Sp K))).hom (Category.comp_id _)
  have h5 := congrArg (fun q => s ≫ q) hx
  simp only [x, comp_toUnit_assoc] at h5
  rw [← Hom.one_def, toUnit_unit, Category.id_comp] at h5
  exact mul_inv_eq_one.1 h5

end GlobalTheory
end
end
