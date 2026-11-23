module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

namespace GlobalTheory.RigidTranslate

open GlobalTheory.PolTranslate ReciprocityTheory.ChartRestriction.G.DVR

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem toUnit_inv_mul_self (a : 𝟙_ (Over S) ⟶ A) (T : Over S) :
    (toUnit T ≫ a⁻¹) * (toUnit T ≫ a) = 1 := by
  rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one]

theorem transl_inv_comp_transl (a : 𝟙_ (Over S) ⟶ A) : transl a⁻¹ ≫ transl a = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]

theorem kTriv_pull_transl (x : 𝟙_ (Over S) ⟶ A) {L : LB A.left} (hL : L.IsLB) (h : Out.KTriv A L) :
    Out.KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x⁻¹).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x⁻¹))) V
  have k₂ : T ◁ transl x⁻¹ ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_inv_comp_transl, Category.comp_id]
  have k₃ : T ◁ transl x⁻¹ ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end

theorem kTriv_rigTransl_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro S A _ L hL a h R _ s y hy
  refine kTriv_pull_transl a hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

end GlobalTheory.RigidTranslate
end

section


theorem _root_.GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArExists := by
  first | exact @GlobalTheory.Published.arExists_of_form_of_mix | exact GlobalTheory.Published.arExists_of_form_of_mix | (intros; apply GlobalTheory.Published.arExists_of_form_of_mix <;> assumption)
end

section


theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  first | exact @GlobalTheory.Published.arShift_of_arChange | exact GlobalTheory.Published.arShift_of_arChange | (intros; apply GlobalTheory.Published.arShift_of_arChange <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  first | exact @GlobalTheory.SelfInterGrowth.main | exact GlobalTheory.SelfInterGrowth.main | (intros; apply GlobalTheory.SelfInterGrowth.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  first | exact @GlobalTheory.GdegPow.gdeg_pow | exact GlobalTheory.GdegPow.gdeg_pow | (intros; apply GlobalTheory.GdegPow.gdeg_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  first | exact @GlobalTheory.DegGrowth.main | exact GlobalTheory.DegGrowth.main | (intros; apply GlobalTheory.DegGrowth.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  first | exact @GlobalTheory.MixHt.exists_linear_of_multiadditive | exact GlobalTheory.MixHt.exists_linear_of_multiadditive | (intros; apply GlobalTheory.MixHt.exists_linear_of_multiadditive <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefPow

theorem height_pow (HE : GlobalTheory.Published.ArExists) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) (L : HermLB p) (n : ℕ)
    {h h' : X → ℝ} (H : L.IsArithHeight h) (H' : (L.pow n).IsArithHeight h') : h' x = n * h x := by
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  rw [← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]

theorem isNef_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  intro HC k _ X _ p D hX M n N
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h₀, H₀⟩ := hex (HermLB.triv p)
    have H : (M.pow 0).IsArithHeight h₀ := M.isometric_pow_zero.symm.isArithHeight hX H₀
    have T := (H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)
    exact (H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩
  · have : Module.Finite ℤ k := hX.finite
    refine ⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical,
      fun Z i _ _ _ hc hd => ?_⟩
    obtain ⟨h, H⟩ := hex M
    obtain ⟨h', H'⟩ := hex (M.pow n)
    obtain ⟨r, hr⟩ := exists_isRatSec ((M.pow n).restr i).isLB
    obtain ⟨r₀, hr₀, h0⟩ := N.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H',
      H.point Z i hc hd r₀ hr₀]
    exact mul_nonneg (Nat.cast_nonneg _) h0

end GlobalTheory.NefPow
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

theorem GlobalTheory.Published.serreHolomorphicSections_holds : GlobalTheory.Published.SerreHolomorphicSections := by
  intro Y p D hs hp R B hB
  refine ⟨fun s t h => ?_, fun s => ?_⟩
  · have e : s.f = t.f := funext fun i => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y _ =>
      congrFun₂ (congrArg Subtype.val h) i y
    cases s; cases t; congr
  have loc (i : B.ι) (x : B.U i) : ∃ V : Y.Opens, x.1 ∈ V ∧ V ≤ B.U i ∧ ∃ c : Γ(Y, V),
      ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = s.1 i y := by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.exists_open_isDomain_of_smooth_complex Y p D hs x
    obtain ⟨V, n, u, hx, hV, ha, h⟩ := GlobalTheory.exists_affine_boundary_functions_of_isProjOver Y p hp (U ⊓ B.U i) x ⟨hxU, x.2⟩
    have hi := hV.trans inf_le_right
    have hd := hU V (hV.trans inf_le_left) hx
    have hh := (s.2.2 i).mono (ptsIn_mono hi)
    obtain ⟨C, m, hC⟩ := GlobalTheory.continuous_section_polynomial_growth Y p hp B hB s.1 s.2.1
      (fun j => (s.2.2 j).continuousOn (isOpen_ptsIn _)) i V n u hi h
    obtain ⟨a, b, hb, e⟩ := SerreSections.exists_mul_eq_of_polynomial_growth Y p D hs R V ha hd _ hh n u C m hC
    exact ⟨V, hx, hi, GlobalTheory.exists_ev_eq_of_continuousOn_quotient Y p D hs V ha hd _ (hh.continuousOn (isOpen_ptsIn _)) a b hb e⟩
  choose V hx hV c hc using loc
  have glue (i : B.ι) : ∃ f : Γ(Y, B.U i), ∀ y ∈ ptsIn p (RingHom.id ℂ) (B.U i),
      ev p (RingHom.id ℂ) _ f y = s.1 i y := by
    obtain ⟨f, hf, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (V i) (B.U i)
      (fun x => homOfLE (hV i x)) (fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx i _⟩) (c i) fun x x' =>
        GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs (V i x ⊓ V i x') _ _ fun y hy =>
          ((ev_res inf_le_left hy _).trans (hc i x y (mem_ptsIn_inf.1 hy).1)).trans
            ((ev_res inf_le_right hy _).trans (hc i x' y (mem_ptsIn_inf.1 hy).2)).symm
    refine ⟨f, fun y hy => ?_⟩
    have hy' : y ∈ ptsIn p (RingHom.id ℂ) (V i ⟨_, mem_ptsIn.1 hy⟩) := mem_ptsIn.2 (hx i _)
    rw [← hc i _ y hy', ← hf]
    exact (ev_res _ hy' _).symm
  choose f hf using glue
  refine ⟨⟨f, fun i j => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y hy => ?_⟩, Subtype.ext (funext₂ fun i y => ?_)⟩
  · have h := mem_ptsIn_inf.1 hy
    refine (ev_res inf_le_left hy _).trans (Eq.trans ?_ (ev_mul _ _ _).symm)
    rw [hf i y h.1, s.2.1.1 i j y h.1 h.2, ← hf j y h.2]
    exact congrArg _ (ev_res inf_le_right hy _).symm
  · by_cases h : y ∈ ptsIn p (RingHom.id ℂ) (B.U i)
    · exact hf i y h
    · exact (ev_of_notMem h _).trans (s.2.1.2 i y h).symm

theorem GlobalTheory.AnRead.bijective_valC {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] (hp : IsProjOver p) (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) :
    Function.Bijective (R.valC B) :=
  GlobalTheory.Published.serreHolomorphicSections_holds.bijective_valC hp R hB
end

section

set_option autoImplicit false

noncomputable section

open Module TensorProduct GlobalTheory.DeRham

namespace GlobalTheory.PrincipalPolPairing

section Algebra

variable {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R' M'] {f : M →ₛₗ[algebraMap R R'] M'}

theorem exists_corr (hf : Function.Bijective (liftSemi f)) (h : Dual R M) :
    ∃ h' : Dual R' M', ∀ c, h' (f c) = algebraMap R R' (h c) := by
  let e := LinearEquiv.ofBijective _ hf
  let l : M →ₛₗ[algebraMap R R'] R' :=
    { toFun c := algebraMap R R' (h c), map_add' := by simp, map_smul' := by simp }
  refine ⟨liftSemi l ∘ₗ e.symm.toLinearMap, fun c ↦ ?_⟩
  have : f c = e (1 ⊗ₜ c) := (one_smul R' (f c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem ext_bc (hf : Function.Bijective (liftSemi f)) {N : Type*} [AddCommGroup N] [Module R' N]
    {u v : M' →ₗ[R'] N} (h : ∀ c, u (f c) = v (f c)) : u = v := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hf.2 c
  induction z with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

theorem ext_corr [Module.Finite R M] [Module.Projective R M] (hf : Function.Bijective (liftSemi f))
    {N : Type*} [AddCommGroup N] [Module R' N] {u v : Dual R' M' →ₗ[R'] N}
    (h : ∀ (y : Dual R M) (y' : Dual R' M'), (∀ c, y' (f c) = algebraMap R R' (y c)) → u y' = v y') :
    u = v := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  choose l hl using fun i : Fin n ↦ exists_corr hf (LinearMap.proj i ∘ₗ s)
  refine LinearMap.ext fun y' ↦ ?_
  have e : y' = ∑ i, y' (f (p (Pi.single i 1))) • l i := by
    refine ext_bc hf fun c ↦ ?_
    have hc : c = ∑ i, s c i • p (Pi.single i 1) := by
      conv_lhs => rw [← LinearMap.id_apply (R := R) c, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s c)]

      simp only [map_sum, map_smul]
    conv_lhs => rw [hc]

    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hl,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]
    simp
  rw [e]

  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h _ _ (hl i)]

theorem subsingleton_of_fibres {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (AlgebraicClosure p.asIdeal.ResidueField ⊗[R] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have := h p
  have e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField p.asIdeal.ResidueField
    (AlgebraicClosure p.asIdeal.ResidueField) Q
  have h₁ := e.toEquiv.subsingleton
  have h₂ : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
    (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.rTensor_nontrivial _ _ _
  exact not_subsingleton _ h₁

end Algebra

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase GlobalTheory.DeRhamSheaf
open Limits (pullback)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Affine

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem isotropic (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg) P hP ψ hψ
  intro x hx y hy
  have := iso _ (push_mem_Fil (inl A A) hx) _ (push_mem_Fil (inr A A) hy)
  rwa [e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, sub_zero] at this

end Affine

end GlobalTheory.PrincipalPolPairing
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal


theorem _root_.GlobalTheory.T.self_dual_lattice_congruence_subgroups : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  first | exact @GlobalTheory.UCls.exists_special_reduction | exact GlobalTheory.UCls.exists_special_reduction | (intros; apply GlobalTheory.UCls.exists_special_reduction <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nontrivial_additive_family_killed_by_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite N.hom → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → i ≠ 1 → ∃ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB ∧ IsAdditive M ∧ Triv (ev M (fst A T ≫ q) (snd A T)) ∧ ¬ Triv M := by
  first | exact @GlobalTheory.CharKer.exists_nontriv_family | exact GlobalTheory.CharKer.exists_nontriv_family | (intros; apply GlobalTheory.CharKer.exists_nontriv_family <;> assumption)
end
