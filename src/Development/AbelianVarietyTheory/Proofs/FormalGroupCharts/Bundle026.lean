module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushChart

theorem prod_ofFn_comp {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {m : ℕ} (u : Fin m → (T ⟶ G)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod := by
  induction m with
  | zero => simp [MonObj.one_comp]
  | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.mul_comp, ih]

theorem isCombAtG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t t' : SAB H X0}
    (ψ : t.G ⟶ t'.G) [IsMonHom ψ] {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {v' : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v' i = v i ≫ ψ.left) {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t' x0 v' cf (w ≫ ψ.left) := by
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => u i ≫ ψ, fun i => ?_, ?_⟩
  · rw [hv, Over.comp_left, hu]
    exact Category.assoc _ _ _
  · rw [← prod_ofFn_comp, Over.comp_left, hw]

theorem isUnivJ_comp {V : Type} [CommRing V] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (ψ : G ≅ G') [IsMonHom ψ.hom]
    {κ : Type} {z : GlobalTheory.PowGerm.JetPts G κ} (h : GlobalTheory.PowGerm.IsUnivJ G κ z) :
    GlobalTheory.PowGerm.IsUnivJ G' κ (fun m => z m ≫ ψ.hom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, h1]
  · rw [← Category.assoc, h2, MonObj.one_comp]
  · intro A _ _ aug m hm y hy
    have hy' : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (y ≫ ψ.inv) = 1 := by
      rw [← cancel_mono ψ.hom, MonObj.one_comp]
      simpa using hy
    obtain ⟨f, ⟨hf1, hf2⟩, hf3⟩ := h3 A aug m hm (y ≫ ψ.inv) hy'
    refine ⟨f, ⟨hf1, ?_⟩, fun g hg => hf3 g ⟨hg.1, ?_⟩⟩
    · rw [← Category.assoc, ← hf2]; simp
    · rw [hg.2]; simp

theorem pushChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), ∃ x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G, (∀ m, (x' m).left = (x m).left ≫ n.φ) ∧ (GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x') ∧ (∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V), IsChartG t (𝟙 (Sp V)) d F act tg uv x → IsChartG t' (𝟙 (Sp V)) d F act (fun l => tg l ≫ n.φ) uv x') ∧ ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u (v ≫ n.φ) := by
  intro E _ _ _ H V _ t t' n d x
  obtain ⟨ψ, hl, hmon, hact, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  have hc : ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v →
      IsCombAtG t' (𝟙 (Sp V)) (dirs fun m => x m ≫ ψ.hom) u (v ≫ n.φ) := by
    intro u v h
    rw [← hl]
    refine isCombAtG_comp ψ.hom _ (fun i => ?_) h
    simp only [dirs, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun m => x m ≫ ψ.hom, fun m => ?_, fun h => isUnivJ_comp ψ h, ?_, hc⟩
  · rw [Over.comp_left, hl]
  · intro F act κ _ tg uv h
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun l => hc _ _ (h.tan l), h.basis⟩
    · rw [← Category.assoc, h.zero, MonObj.one_comp]
    · rw [← Category.assoc, h.trunc]
    · rw [← Category.assoc, h.law, MonObj.mul_comp]
      simp only [jptG, Category.assoc]
    · rw [Category.assoc, ← hact, ← Category.assoc, h.act, Category.assoc]

end GlobalTheory.PushChart
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet

namespace GlobalTheory.ChartCmp.CoordDir

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}

def tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (g : Fin 1 × Fin d → V) :
    overAt (𝟙 (Sp V)) (DualNumber V) ⟶ t.G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1

theorem tp_zero : (tp (0 : Fin 1 × Fin d → V)) =
      (Algebra.ofId V (DualNumber V)).comp (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [tp_mk, AlgHom.comp_apply]
  show TrivSqZeroExt.inr (0 : V) =
    algebraMap V (DualNumber V) (MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q))
  rw [MvPolynomial.aeval_X, map_zero, TrivSqZeroExt.inr_zero]

theorem fst_tp (g : Fin 1 × Fin d → V) : (TrivSqZeroExt.fstHom V V V).comp (tp g) =
      (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [AlgHom.comp_apply, tp_mk]
  show (0 : V) = MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q)
  rw [MvPolynomial.aeval_X]

variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}

theorem tanPt_zero (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : tanPt x 0 = 1 := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.zero 1
  rw [tanPt, tp_zero, ← GermD.homAt_comp, Category.assoc, hz, MonObj.comp_one]

theorem tanPt_add (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) (g g' : Fin 1 × Fin d → V) :
    tanPt x (g + g') = tanPt x g * tanPt x g' := by
  let T : Jet V (Fin 2 × Fin d) (0 + 1) →ₐ[V] DualNumber V :=
    tp (fun p : Fin 2 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2)
  have hT : T = tp (fun p : Fin 2 × Fin d =>
    (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2) := rfl
  have hc : ∀ i : Fin 2, T.comp (jetCopy d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, hT, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 0 q.2) = tp g := by
    congr 1
    funext ⟨i, j⟩
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h1 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 1 q.2) = tp g' := by
    congr 1
    funext ⟨i, j⟩
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hF : T.comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => G.F p.2) (fun p => G.const p.2),
      hT, tp_psJet, tp_mk, G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) ≫ x 1 =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (0 : Fin 2)) ≫ x 1) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (1 : Fin 2)) ≫ x 1) :=
    hx.law 1
  have e := congrArg (fun f => Formalism.L2.Pj.homAt (𝟙 (Sp V)) T ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e

theorem tanPt_sum (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : ∀ (n : ℕ) (f : Fin n → Fin 1 × Fin d → V),
    tanPt x (∑ i, f i) = (List.ofFn fun i => tanPt x (f i)).prod
  | 0, f => by rw [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil, tanPt_zero hx]
  | n + 1, f => by rw [Fin.sum_univ_succ, tanPt_add hx, tanPt_sum hx n, List.ofFn_succ, List.prod_cons]

theorem eps_tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (a : V) (g : Fin 1 × Fin d → V) :
    spMap (epsMul a) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1).left = (tanPt x (a • g)).left := by
  have h : (TrivSqZeroExt.map (a • LinearMap.id : V →ₗ[V] V)).comp (tp g) = tp (a • g) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, tp_mk, tp_mk, TrivSqZeroExt.map_inr]
    rfl
  rw [tanPt, ← h]
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left, ← Category.assoc, spMap, epsMul, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem comb_eq (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) {u : Fin d → V} {v : Sp (DualNumber V) ⟶ t.G.left}
    (h : IsCombAtG t (𝟙 (Sp V)) (dirs x) u v) : (tanPt x fun q => u q.2).left = v := by
  obtain ⟨w, hw, hprod⟩ := h
  have hw' : w = fun i => tanPt x (u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hw i, dirs, jetTan_eq_tp, eps_tanPt]
  have hq : ∀ (q : Fin 1 × Fin d) (i : Fin d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs : (∑ i, u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) =
      fun q => u q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [← hs, tanPt_sum hx, ← hprod, hw']

theorem tanPt_rel {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {φ : Pt V 1 d}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (h : CoordRel x x' φ) (u : Fin d → V) :
    tanPt x' (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u q.2) := by
  have hF : (tp (fun q : Fin 1 × Fin d => u q.2)).comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) =
      tp (fun q : Fin 1 × Fin d => (dLin φ).mulVec u q.2) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => φ p.2) (fun p => hφ p.2),
      tp_psJet, tp_mk, hφ, TrivSqZeroExt.inl_zero, zero_add]
    congr 1
    simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mulVec, dotProduct, dLin]
    exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
  have h1 : x' 1 = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) ≫ x 1 := h 1
  rw [tanPt, tanPt, h1, ← Category.assoc, GermD.homAt_comp, hF]

theorem tanPt_inj {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} (hx : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x)
    {g g' : Fin 1 × Fin d → V} (h : tanPt x g = tanPt x g') : g = g' := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.2.1 1
  have h0 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (TrivSqZeroExt.fstHom V V V) ≫ tanPt x g = 1 := by
    rw [tanPt, ← Category.assoc, GermD.homAt_comp, fst_tp, hz]
  have e : tp g = tp g' :=
    (hx.2.2 (DualNumber V) (TrivSqZeroExt.fstHom V V V) (0 + 1) ker_fst_sq (tanPt x g) h0).unique
      ⟨fst_tp g, rfl⟩ ⟨fst_tp g', h⟩
  funext q
  have := congrArg (fun ψ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V =>
    ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) e
  simp only [tp_mk] at this
  exact TrivSqZeroExt.inr_injective this

end

theorem coord_dir : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ hx hx' hU hφ hrel u u' v hu hu'
  have e : tanPt x (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u' q.2) := by
    rw [← tanPt_rel hφ hrel]
    apply Over.OverMorphism.ext
    rw [comb_eq hx hu, comb_eq hx' hu']
  funext j
  exact congrFun (tanPt_inj hU e) (0, j)

end GlobalTheory.ChartCmp.CoordDir
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V] {d : ℕ}

theorem ev_one_eq {n : ℕ} (a : Pt V n d) (f : PS V 1 d) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin d => a p.2) f := by
  unfold ev
  congr 1
  funext p
  rw [Matrix.cons_val_fin_one]

theorem cc_ev {k n : ℕ} (a : Fin k → Pt V n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS V k d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem cc_comp1 {n : ℕ} {φ : Pt V 1 d} {a : Pt V n d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) : MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by rw [Matrix.cons_val_fin_one]; exact ha i) _ (hφ i)

theorem germCompOne_assoc_of_constantCoeff_zero {n : ℕ} (ψ φ : Pt V 1 d) (a : Pt V n d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : comp1 (comp1 ψ φ) a = comp1 ψ (comp1 φ a) := by
  funext i
  simp only [comp1, ev_one_eq]
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => hφ p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem germCompOne_identityPoint_left {n : ℕ} (a : Pt V n d) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    comp1 (pt V (n := 1) d 0) a = a := by
  funext i
  simp only [comp1, ev_one_eq, pt]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem eq_comp1_inv {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by
  rw [← e, ← germCompOne_assoc_of_constantCoeff_zero φi φ a h.1 ha, h.2.2.2, germCompOne_identityPoint_left a ha]

def sub (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m k :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin k × Fin d => a p.1 p.2)

def sub1 (m : ℕ) {n : ℕ} (a : Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m 1 :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d => a p.2)

theorem hom_comp (m : ℕ) {κ κ' κ'' : Type} [Fintype κ'] [DecidableEq κ'] [Fintype κ''] [DecidableEq κ'']
    (g : κ → MvPowerSeries κ' V) (h : κ' → MvPowerSeries κ'' V) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) h) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) g) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun i => MvPowerSeries.subst h (g i)) := by
  rw [GermD.homAt_comp]
  congr 1
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m g hg, ExpChartJet.jetSubstPS_psJet m h hh,
    ExpChartJet.jetSubstPS_mk m _ (fun i => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hh) hh (hg i))]

theorem jetSchemeMap_pointFamily_comp_singlePoint (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) (b : Pt V k d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    sub m a ≫ sub1 m b = sub1 m (fun i => ev a (b i)) :=
  hom_comp m _ _ (fun p => hb p.2) (fun p => ha p.1 p.2)

theorem jetSchemeMap_singlePoint_comp_singlePoint (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by
  have e : sub1 m (comp1 φ a) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d =>
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => a q.2) (φ p.2)) := by
    simp only [sub1, comp1, ev_one_eq]
  rw [e]
  exact hom_comp m _ _ (fun p => hφ p.2) (fun p => ha p.2)

theorem eq_of_jetSchemeMap_singlePoint_universal {G : Over (Sp V)} [GrpObj G] {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {n : ℕ} {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (h : ∀ m, sub1 m a ≫ x m = sub1 m b ≫ x m) : a = b := by
  funext i
  refine GermFun.psJet_inj fun m => ?_
  have hk : RingHom.ker (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ^ (m + 1) = ⊥ := by
    have ea : (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) = Chart.jetAug V _ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow _ m
  have aa := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2)
  have ab := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)
  have h1 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ≫ (sub1 m a ≫ x m) = 1 := by
    rw [sub1, ← Category.assoc, GermD.homAt_comp, aa]
    exact hx.2.1 m
  have e := (hx.2.2 _ jetAug m hk _ h1).unique ⟨aa, rfl⟩ ⟨ab, h m⟩
  have e' := AlgHom.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2),
    ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)] at e'

theorem jptG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (m : ℕ) {n : ℕ} (i : Fin n) :
    jptG t (𝟙 (Sp V)) d x m i = sub1 m (pt V d i) ≫ x m := by
  have e : jetCopy (S := V) d m i = jetSubstPS (m := m) (fun p : Fin 1 × Fin d => pt V d i p.2) := by
    apply GermD.jet_hom_ext
    intro p
    rw [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => pt V d i p.2) (fun _ => MvPowerSeries.constantCoeff_X _),
      jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X, pt, ← MvPolynomial.coe_X]
    rw [psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rw [jptG, e]
  rfl

end GlobalTheory.ChartCmp.CoordLaw


open GlobalTheory.ChartCmp.CoordLaw in
theorem GlobalTheory.ChartCmp.law_act_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ φi hc hc' hu hinv hrel
  have hφ := hinv.1
  have hr : ∀ m, x' m = sub1 m φ ≫ x m := hrel
  have hpt : ∀ (j : Fin 2) i, MvPowerSeries.constantCoeff (pt V d j i) = 0 := fun j i => MvPowerSeries.constantCoeff_X _
  refine ⟨?_, fun a => ?_⟩
  · let A : Fin 2 → Pt V 2 d := ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)]
    have hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0 := by
      intro j i
      fin_cases j <;> exact cc_comp1 hφ (hpt _) i
    have hX : ∀ j, (fun i => ev A (pt V d j i)) = A j := fun j => funext fun i =>
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 2 × Fin d => hA p.1 p.2) (j, i)
    have key : comp1 φ B'.G.F = addOf B.G.F (comp1 φ (pt V (n := 2) d 0)) (comp1 φ (pt V (n := 2) d 1)) := by
      refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ B'.G.const) (fun i => cc_ev A hA _ (B.G.const i)) fun m => ?_
      have l : sub1 m B.G.F ≫ x m = _ := hc.law m
      have l' : sub1 m B'.G.F ≫ x' m = _ := hc'.law m
      have l2 := congrArg (fun f => sub m A ≫ f) l
      simp only [jptG_eq, MonObj.comp_mul, ← Category.assoc, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA B.G.const, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA (hpt _),
        hX] at l2
      simp only [jptG_eq, hr m, ← Category.assoc, jetSchemeMap_singlePoint_comp_singlePoint m _ φ B'.G.const hφ, jetSchemeMap_singlePoint_comp_singlePoint m _ φ (hpt _) hφ] at l'
      exact l'.trans l2.symm
    exact fun i => congrFun (eq_comp1_inv hinv B'.G.const key) i
  · refine eq_comp1_inv hinv (B'.A.const a) ?_
    refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ (B'.A.const a)) (cc_comp1 (B.A.const a) hφ) fun m => ?_
    have l : x m ≫ t.act.act a = sub1 m (B.A.act a) ≫ x m := hc.act m a
    have l' : x' m ≫ t.act.act a = sub1 m (B'.A.act a) ≫ x' m := hc'.act m a
    rw [← jetSchemeMap_singlePoint_comp_singlePoint m _ φ (B'.A.const a) hφ, ← jetSchemeMap_singlePoint_comp_singlePoint m φ _ hφ (B.A.const a), Category.assoc, Category.assoc, ← hr m,
      ← l', ← l, hr m, Category.assoc]
end
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem exists_corr_of_family_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    (h : φ = φ') (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c c' := by
  subst h
  refine ⟨c, hc, fun j j' _ _ hj => ?_⟩
  obtain rfl : j = j' := funext fun k => hj k k rfl
  rfl

theorem exists_pushFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  intro E _ _ _ H V _ t t' n w d x x' e hw hx he
  obtain ⟨ψ, hψ, hmon, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  haveI : IsIso n.φ := by
    rw [← hψ]
    exact inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hcar := (GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => by
    ext1
    rw [hx, Over.comp_left, hψ]
  have hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) =
      cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] := fun m => by
    funext J
    have hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) =
        fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom := by
      funext k
      fin_cases k <;> simp [jptG, hx']
    rw [hv]
    simp only [cφG, psum]
    rw [← hψ, ← Over.comp_left, foldr_padd_comp]
  have key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
      c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)])
        (cε 2) (e m) c := fun m => by
    obtain ⟨c, hc, hcc⟩ := hcar _ _
      (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)
    obtain ⟨e', he', hce⟩ := exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc
    exact ⟨e', he', c, hc, hce, hcc⟩
  choose e' he' using key
  exact ⟨e', he'⟩

end GlobalTheory.ChartCmp
end
