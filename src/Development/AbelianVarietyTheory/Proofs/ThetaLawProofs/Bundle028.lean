module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaNormalFormTranslateHalfPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopLeTranslate
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle016
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero
open GlobalTheory.KeyKa.EtBaseChange

section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem map_mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hV : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((Units.isUnit (w.s (fun _ => k, i))).pow l)).ge hV
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hV, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

theorem exists_gs_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (c : x.P.L.ι) (c' : x'.P.L.ι) (h : φ y ∈ x.P.L.U c) (h' : y ∈ x'.P.L.U c') :
    ∃ u, IsUnit u ∧ gs φ y (x.P.L.U c) (s.f c) = u * gs (𝟙 _) y (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hV : (𝟙 x'.P.A.left : _ ⟶ _) y ∈ (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' := ⟨mem_pull.2 h, h'⟩
  have e := congrArg (gs (𝟙 _) y _) (hs (fun _ => c) c' hle)
  have e₁ := (gs_res (𝟙 _) y hle hV ((φ.app _).hom (s.f c))).trans (gs_pull (𝟙 _) φ y _ h (s.f c))
  rw [Category.id_comp] at e₁
  refine ⟨_, ?_, e₁.symm.trans (e.trans ((gs_mul _ _ _ hV _ _).trans
    (congrArg (_ * ·) (gs_res (𝟙 _) y inf_le_right hV _))))⟩
  rw [gs_eq _ _ _ hV]
  exact (((Units.isUnit (w.s (fun _ => c, c'))).pow l).map _).map _

end Via

theorem exists_lift_point {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {x : KeyIn O} {xk : KeyIn (IsLocalRing.ResidueField O)} {φ w}
    {n : ℕ} (hg : xk.P.g = x.P.g) {s : Fin x.P.g → RR x n} {sk : Fin xk.P.g → RR xk n}
    (hvia : KeyVia xk x (IsLocalRing.residue O) φ w) (hs : ∀ i, SecVia xk x φ w (sk i) (s (i.cast hg)))
    (zk : Pt xk) (c' : xk.P.L.ι) (h₁ : ⊤ ≤ zk.left ⁻¹ᵁ xk.P.L.U c')
    (h₂ : ∀ i, valT (T := IsLocalRing.ResidueField O) zk.left (xk.P.L.U c') ((sk i).f c') = 0)
    (h₃ : IsUnit (jac xk sk zk c')) :
    ∃ (z : Pt x) (c : x.P.L.ι), spMap (IsLocalRing.residue O) ≫ z.left = zk.left ≫ φ ∧ ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧
      (∀ i, valT (T := O) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ IsUnit (jac x s z c) ∧
      ∀ (y : x.P.A.left) (pt : Sp (IsLocalRing.ResidueField O)), y ⤳ φ (zk.left pt) →
        (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ r : Sp O, z.left r = y := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := hvia
  have := x.P.isAb.smooth
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hpt : ∀ r : Sp (IsLocalRing.ResidueField O), r = pt := fun r =>
    Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField O)) _ _
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (φ (zk.left pt))
  have hc' : zk.left pt ∈ xk.P.L.U c' := h₁ (x := pt) trivial
  have hφ : ⊤ ≤ (zk.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun r _ => by
    obtain rfl := hpt r
    exact hc
  have hW := le_inf_pull (T := IsLocalRing.ResidueField O) zk.left c c' hφ h₁
  let u := Units.map (valH (T := IsLocalRing.ResidueField O) zk.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := IsLocalRing.ResidueField O) zk.left ((x.P.L.pull φ).U (fun _ => c) ⊓ xk.P.L.U c')
      (w.s (fun _ => c, c')).val = u := valT_eq _ _ hW _
  have hd : (Matrix.of fun i k => (valT (T := DualNumber (IsLocalRing.ResidueField O))
      (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) (x.P.L.U c) ((s (i.cast hg)).f c)).snd).det ≠ 0 := by
    refine fun h => mul_ne_zero (pow_ne_zero (Fintype.card (Fin xk.P.g)) (pow_ne_zero n u.ne_zero)) h₃.ne_zero
      ((Matrix.det_smul _ _).symm.trans (Eq.trans ?_ h))
    congr 1
    ext i k
    have l₂ := translate_le zk (xk.v k) (xk.basis.1 _) h₁
    have l₃ : ⊤ ≤ (((toUnit (epsR _) ≫ zk) * xk.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c :=
      translate_le zk (xk.v k) (xk.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
    have e := valT_via (T := DualNumber (IsLocalRing.ResidueField O)) (hs i) _ c c' l₃ l₂
    refine Eq.symm ((congrArg TrivSqZeroExt.snd e).trans ?_)
    refine (snd_pow_mul _ _ _ ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) h₁ _).trans (h₂ i))).trans ?_
    exact congrArg (· ^ n * _) ((fst_valT_translate zk (xk.v k) (xk.basis.1 _) hW _).trans hu)
  obtain ⟨z₀, hz₁, hz₂, hz₃, hz₄⟩ := exists_section_of_transversal hp.1 zk.left (Over.w zk) pt hc
    (fun i : Fin xk.P.g => (s (i.cast hg)).f c)
    (fun i => (valT_via (T := IsLocalRing.ResidueField O) (hs i) zk.left c c' hφ h₁).trans
      (mul_eq_zero_of_right _ (h₂ i)))
    (by
      rw [← (jac_ne_zero_iff_span_eq_maximalIdeal _ xk n sk zk c' pt h₁ h₂).1 h₃.ne_zero]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨v, hv, e⟩ := exists_gs_via (hs i) (zk.left pt) c c' hc hc'
      exact (Ideal.unit_mul_mem_iff_mem _ hv).1 (Ideal.subset_span ⟨i, e⟩))
    (fun k => ((toUnit (epsR _) ≫ zk) * xk.v k).left)
    (fun k => fst_comp_translate zk (xk.v k) (xk.basis.1 _)) (fun k => Over.w ((toUnit (epsR _) ≫ zk) * xk.v k)) hd
  let z : Pt x := Over.homMk z₀ hz₁
  have hz : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := (Scheme.preimage_eq_top_of_closedPoint_mem z₀ (by
    rw [← IsLocalRing.comap_closedPoint (IsLocalRing.residue O)]
    exact (congrArg (fun g => g pt ∈ x.P.L.U c) hz₂).ge hc)).ge
  refine ⟨z, c, hz₂, hz, fun i => hz₃ (i.cast hg.symm), ?_, fun y r hy hy' => ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    refine fun h => hd (Eq.trans ?_ h)
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg)]
    congr 1
    ext i k
    have e := translate_comp hp F hF₁ z zk hz₂.symm (x.v (k.cast hg)) (xk.v k) (hv k)
    have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) hz
    have e₂ := (congrArg (fun q => valT (T := DualNumber (IsLocalRing.ResidueField O)) q (x.P.L.U c)
      ((s (i.cast hg)).f c)) e).trans (valT_spMap F _ l₁ _)
    exact (congrArg TrivSqZeroExt.snd e₂).trans (snd_map _ F hF₁ hF₂ _)
  · obtain rfl := hpt r
    exact hz₄ y hy fun i h => hy' (i.cast hg) (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)

end GlobalTheory.HenselZero


open GlobalTheory.HenselZero in
theorem GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro O _ _ _ _ x xk φ w n d hg s sk zk chk hvia hs ⟨h₁, h₂, h₃, h₄, h₅⟩
  choose z ch hz₀ hz₁ hz₂ hz₃ hz₄ using fun a => exists_lift_point hg hvia hs (zk a) (chk a) (h₁ a) (h₂ a) (h₃ a)
  obtain ⟨_, _, _, ⟨hp, -⟩, -⟩ := hvia
  have := x.P.isAb.proper
  have := isClosedImmersion_fibre hp
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hcp : spMap (IsLocalRing.residue O) pt = IsLocalRing.closedPoint O :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have hw : ∀ a, (z a).left ≫ x.P.A.hom = 𝟙 (Sp O) := fun a => Over.w (z a)
  have hzc : ∀ a, (z a).left (IsLocalRing.closedPoint O) = φ ((zk a).left pt) := fun a =>
    (congrArg (z a).left hcp).symm.trans (congrArg (fun g => g pt) (hz₀ a))
  refine ⟨z, ch, hz₁, hz₂, hz₃, fun a a' h r e => h₄ a a' h pt (φ.isClosedEmbedding.injective ?_), fun y hy => ?_⟩
  · have : IsClosedImmersion ((z a').left ≫ x.P.A.hom) := by
      rw [hw]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp O) : Sp O ⟶ Sp O))
    have := IsClosedImmersion.of_comp (z a').left x.P.A.hom
    obtain ⟨r', hr'⟩ := ((IsLocalRing.specializes_closedPoint r).map (z a).left.continuous).mem_closed
      (z a').left.isClosedEmbedding.isClosed_range ⟨r, e.symm⟩
    have e₁ : r' = IsLocalRing.closedPoint O :=
      (congrArg (fun g => g r') (hw a')).symm.trans ((congrArg x.P.A.hom hr').trans
        (congrArg (fun g => g (IsLocalRing.closedPoint O)) (hw a)))
    rw [← hzc, ← hzc, ← hr', e₁]
  · obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (x.P.A.hom y)).mem_closed
      (x.P.A.hom.isClosedMap _ (isClosed_closure (s := {y}))) ⟨y, subset_closure rfl, rfl⟩
    have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y₀ pt (e.trans hcp.symm)
    obtain ⟨a, r, rfl⟩ := h₅ y' fun i h => hy (i.cast hg)
      (hsp.mem_open (Out.nonzeroLocus _).isOpen (map_mem_nonzeroLocus_via (hs i) y' h))
    exact ⟨a, hz₄ a y r hsp hy⟩

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.boxProducts_basis_span_powObj_sections : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  first | exact @GlobalTheory.BoxSpan.boxProducts_span | exact GlobalTheory.BoxSpan.boxProducts_span | (intros; apply GlobalTheory.BoxSpan.boxProducts_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.geom_integral_of_etale_faithfully_flat_cover : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  first | exact @GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | exact GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale | (intros; apply GlobalTheory.KeyFam.exists_geomInt_piece_of_finite_etale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KaUnique

theorem exists_perm {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x}
    {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch') :
    ∃ σ : Equiv.Perm (Fin d), ∀ a, z' (σ a) = z a := by
  let p : Sp K := IsLocalRing.closedPoint K
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  have h1 : ∀ a, ∃ a', z' a' = z a := by
    intro a
    obtain ⟨a', q, hq⟩ := hz'.2.2.2.2 ((z a).left p) (fun i hi => by
      obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
      have hcU : ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U c := fun q _ => by
        rw [hs q p]; exact x.P.A.left.basicOpen_le _ hc
      have e := valT_sec (T := K) (z a).left x.P.L c (ch a) hcU (hz.1 a) n (s i)
      erw [hz.2.1 a i, mul_zero, valT_eq _ _ hcU] at e
      have e1 : IsUnit (evalHom (T := K) (z a).left (x.P.L.U c) hcU ((s i).f c)) ↔
          IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) :=
        isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
      have e2 := Scheme.basicOpen_appLE (show Sp K ⟶ x.P.A.left from (z a).left) ⊤ (x.P.L.U c) hcU ((s i).f c)
      have e3 : IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
        apply RingedSpace.isUnit_of_isUnit_germ
        intro q hq
        have : q ∈ (Sp K).basicOpen
            (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
          erw [e2]; rw [hs q p]; exact ⟨trivial, hc⟩
        exact ((Sp K).mem_basicOpen _ q hq).1 this
      exact (e1.2 e3).ne_zero e)
    exact ⟨a', Over.OverMorphism.ext (section_ext x.P.A.hom _ _ (Over.w (z' a')) (Over.w (z a)) q p hq)⟩
  choose f hf using h1
  have hinj : Function.Injective f := fun a a' e => by
    by_contra hne
    exact hz.2.2.2.1 a a' hne p (by rw [← hf a, ← hf a', e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem degree_compare (hL : Out.Laws) {K : Type} [Field K] [CharZero K] (x : KeyIn K) {n l d : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hl : x.P.g * n < l)
    {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x} {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch')
    (σ : Equiv.Perm (Fin d)) (ga : Fin d → Kˣ)
    (hga : ∀ a (r : RR x (l - 0 * n)), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ (l - 0 * n) * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))))
    {b b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {t t' : Kˣ} {lam lam' : ℕ → Kˣ}
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j))
    (hb' : ∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b' j) (lam' j))
    (ht : KosVal x l s z ch b t) (ht' : KosVal x l s z' ch' b' t') :
    ∃ be : ℕ → Kˣ, t' = t * (∏ a, ga a) ^ (-2 * (l : ℤ)) * 1 ^ 2 *
        ∏ j ∈ Finset.range (x.P.g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (x.P.g.choose j : ℤ)) ∧
      ∀ j ≤ x.P.g, lam' j = lam j * be j ^ (-8 * ((l - j * n) ^ (3 * x.P.g + 2) : ℕ) : ℤ) *
        1 ^ (8 * (l - j * n) ^ (4 * x.P.g + 2)) := by
  have hB : ∀ j, ∃ B : (Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j * n) ^ x.P.g)) K)ˣ, j ≤ x.P.g →
      ∀ k, IsComb x.P.A.hom x.P.L (fam x (b j)) (fun k' => B.val k' k) (fam x (b' j) k) := fun j => by
    by_cases hj : j ≤ x.P.g
    · obtain ⟨B, hB⟩ := exists_change (hb j hj).1 (hb' j hj).1
      exact ⟨B, fun _ => hB⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose B hB using hB
  obtain ⟨m, hm, ht⟩ := ht
  obtain ⟨m', hm', ht'⟩ := ht'
  let P : Matrix (Fin d) (Fin d) K := (Matrix.diagonal fun a => (ga a).val ^ (l - 0 * n)).submatrix id σ.symm
  have hP : P.det ^ 2 = (((∏ a, ga a) ^ (2 * l) : Kˣ) : K) := by
    simp only [P]
    rw [Matrix.det_permute', Matrix.det_diagonal, mul_pow, Finset.prod_pow, ← pow_mul]
    have : ((Equiv.Perm.sign σ.symm : ℤ) : K) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
    rw [this]
    simp [mul_comm]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2
    ((isUnit_pow_iff two_ne_zero).1 (hP ▸ Units.isUnit _))
  obtain ⟨t'', h1, h2⟩ := GlobalTheory.KeyKa.torsSq_kosD_conj K x.P.g d (fun j => (l - j * n) ^ x.P.g) m m' _
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x.P.L.U (ch' a)) ((b' j k).f (ch' a))) B hPu.unit t
    (fun i j hj => by
      ext a k
      have e1 := IsComb.mulVec' (hB j hj.le) (isMul_comb hm' i j hj k)
      have e2 := IsComb.mulVec (isMul_comb hm i j hj) (hB (j + 1) hj k)
      exact congrFun (comb_unique (hb j hj.le).1 e1 e2) a)
    (by
      ext a k
      have e1 := (hB 0 (Nat.zero_le _) k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
      refine Eq.trans ?_ e1
      refine Eq.trans ?_ (hga a (b' 0 k)).symm
      rw [IsUnit.unit_spec, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
      · simp [P]
      · intro a' _ h
        have : a ≠ σ.symm a' := fun e => h (by rw [e, Equiv.apply_symm_apply])
        simp [P, Matrix.diagonal_apply_ne _ this]
      · intro h; exact absurd (Finset.mem_univ _) h)
    (isCx_of_isMul hm (fun j hj => (hb j hj).1) hz) ht
  have h3 : t'' = t' := Units.ext (GlobalTheory.TorsionUnique.torsSq_unique K _ _ _ _ _
    (isCx_of_isMul hm' (fun j hj => (hb' j hj).1) hz') h1 ht').1
  subst h3
  have h4 : Matrix.GeneralLinearGroup.det hPu.unit ^ 2 = (∏ a, ga a) ^ (2 * l) := Units.ext hP
  refine ⟨fun j => Matrix.GeneralLinearGroup.det (B j), ?_, fun j hj => ?_⟩
  · rw [h4] at h2
    rw [one_pow, _root_.mul_one, mul_right_comm, ← h2, neg_mul, zpow_neg]
    have : (∏ a, ga a) ^ (2 * (l : ℤ)) = (∏ a, ga a) ^ (2 * l) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [this, mul_inv_cancel_right]
  · rw [one_pow, _root_.mul_one]
    have hpos : l - j * n ≠ 0 := by
      have : j * n ≤ x.P.g * n := Nat.mul_le_mul_right _ hj
      omega
    exact GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change hL K x (l - j * n) _ (b j) (b' j) (B j) _ _ (Nat.cast_ne_zero.2 hpos) (hal _) (hb j hj).1
      (hB j hj) (hb j hj).2 (hb' j hj).2

theorem tComb_congr {R : Type} [CommRing R] (g n l Pr : ℕ) (t : Rˣ) {lam mu : ℕ → Rˣ} (h : ∀ j ≤ g, lam j = mu j) :
    tComb g n l Pr t lam = tComb g n l Pr t mu := by
  unfold tComb
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

theorem kaVal_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  intro hL K _ _ x n l l' al s κ κ' ⟨_, hl, hl', hal⟩
    ⟨z, ch, b₁, b₂, t₁, t₂, J, lam₁, lam₂, hz, hJ, hb₁, hb₂, ht₁, ht₂, hκ⟩
    ⟨z', ch', b₁', b₂', t₁', t₂', J', lam₁', lam₂', hz', hJ', hb₁', hb₂', ht₁', ht₂', hκ'⟩
  obtain ⟨σ, hσ⟩ := exists_perm hz hz'
  have hc : ∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch' (σ a)) := fun a => hσ a ▸ hz'.1 (σ a)
  let ga := fun a => trU (T := K) (z a).left x.P.L (ch a) (ch' (σ a)) (hz.1 a) (hc a)
  have hga : ∀ (k : ℕ) a (r : RR x k), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ k * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))) := fun k a r => by
    rw [hσ a]
    exact valT_sec (T := K) (z a).left x.P.L _ _ (hz.1 a) (hc a) k r
  obtain ⟨be₁, e₁, f₁⟩ := degree_compare hL x hal hl hz hz' σ ga (hga _) hb₁ hb₁' ht₁ ht₁'
  obtain ⟨be₂, e₂, f₂⟩ := degree_compare hL x hal (hl.trans hl') hz hz' σ ga (hga _) hb₂ hb₂' ht₂ ht₂'
  have eJ : J' = J * (∏ a, ga a) ^ (-((x.P.g * n : ℕ) : ℤ)) * 1 ^ 2 := by
    rw [one_pow, _root_.mul_one, zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, hJ, hJ', ← Equiv.prod_comp σ, Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have h0 := hz'.2.1 (σ a)
    rw [hσ a] at h0 ⊢
    rw [jac_chart x s (z a) (ch a) (ch' (σ a)) (hz.1 a) (hc a) h0, mul_comm]
  have key := GlobalTheory.kaForm_homogeneous K x.P.g n l l' t₁ t₂ J (∏ a, ga a) 1 1 lam₁ lam₂ be₁ be₂ hl hl'
  rw [one_pow (8 * kaExp _ _ _ _), _root_.mul_one, ← e₁, ← e₂, ← eJ] at key
  rw [hκ, hκ', ← key]
  unfold kaForm
  rw [tComb_congr _ _ _ _ t₁' f₁, tComb_congr _ _ _ _ t₂' f₂]

end GlobalTheory.KaUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

theorem _root_.GlobalTheory.T.thetaNormalForm_translate_halfPeriod : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (g : ℕ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b a' b' : Fin g → ℂ) (m n : Fin g → ℤ) (ν : ℂˣ), charHalf g a b → charHalf g a' b' → Wit x h u τ a b → (∀ i, ∃ k : ℤ, a' i = a i + n i / 2 + k) → (∀ i, ∃ k : ℤ, b' i = b i + m i / 2 + k) → IsTrl x' x (u.ex (frac τ 2 m n)) ν → ∃ (h' : x'.P.g = g) (u' : HolUnif x'.P.A x'.P.L g) (φ : x'.P.A ≅ x.P.A) (c : ℂ), IsMonHom φ.hom ∧ (∀ z, u'.ex z ≫ φ.hom = u.ex z) ∧ c ^ 8 * (ν : ℂ) ^ 2 = 1 ∧ (∀ z, z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th (fun z => c * thetaChar τ a' b' z) ∧ ∀ i : Fin g, u'.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x'.v (i.cast h'.symm)) := by
  first | exact @GlobalTheory.HalfTranslate.normalForm_translate | exact GlobalTheory.HalfTranslate.normalForm_translate | (intros; apply GlobalTheory.HalfTranslate.normalForm_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta


theorem _root_.GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  first | exact @GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | exact GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | (intros; apply GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul <;> assumption)
end

section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem powObj_smoothOfRelativeDimension_mul : ∀ (S : Scheme.{0}) (A : Over S) (g j : ℕ),
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension (j * g) (Out.powObj A j).hom :=
  fun _ A g j h => smoothOfRelativeDimension_powObj A g h j

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyPBScale

theorem appLE_constFn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {X Y : Scheme.{0}} {φ : Y ⟶ X}
    (p : X ⟶ Sp R) (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (a : R) : (φ.appLE U V h).hom (constFn p U a) = constFn p' V (f a) :=
  KeyVia.appLE_cst f p p' hφ h a

theorem resG_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  KeyVia.res_appLE (φ := p) (U := ⊤) (fun _ _ => trivial) h _

theorem lie_baseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (hu : ∀ i : Fin m, IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left) (i : Fin m) :
    (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).2 (hu i)

theorem keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R) (M : Matrix (Fin P.g) (Fin P.g) R) (Q : Out.PolAV (Sp R')) (e : Q.g = P.g) (hgQ rigQ hrQ s hs u hu s' hs' u' hu'), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → (∀ i, LB.Sec.f s' i = constFn Q.A.hom _ (f a) * LB.Sec.f s i) → (∀ i : Fin Q.g, IsLieComb (fun j : Fin Q.g => f (M (i.cast e) (j.cast e))) u (u' i)) → KeyPB (⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ : KeyIn R') (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f → KeyPB (⟨Q, hgQ, rigQ, hrQ, s', hs', u', hu'⟩ : KeyIn R') (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f := by
  intro R R' _ _ f P hg rig hr th hth v hv th' hth' v' hv' a M Q e hgQ rigQ hrQ s hs u hu s' hs' u' hu' h₁ h₂ h₃ h₄
  rintro ⟨φ, he, w, hg', F, hp, hw, hrig, hsec, hF, hε, hlie⟩
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  refine ⟨φ, he, w, hg', F, hp, hw, hrig, fun j i h => ?_, hF, hε, ?_⟩
  · have k := hsec j i h
    dsimp only at k ⊢
    rw [h₁, h₃, map_mul, map_mul, k, appLE_constFn f P.A.hom Q.A.hom hp.1.w, resG_constFn]
    exact mul_left_comm (G := Γ(Q.A.left, (P.L.pull φ).U j ⊓ Q.L.U i)) _ _ _
  · subst hF'
    exact lie_baseChange f hp e M v v' u u' h₂ h₄ hlie

end GlobalTheory.KeyPBScale
end
end
