module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle693
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle700
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle641
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := GlobalTheory.T.projective_bundle_points_of_rational_model F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, GlobalTheory.T.geometricallyIntegral_of_affCover F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, GlobalTheory.T.isFlagRefinementBundle_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := GlobalTheory.T.exists_graded_line_divisors_full_flag E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

end GlobalTheory.FlagBundle
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.torus_coord_squares_correspond' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  first | exact @GlobalTheory.torus_coord_squares_correspond | exact GlobalTheory.torus_coord_squares_correspond | (intros; apply GlobalTheory.torus_coord_squares_correspond <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | exact GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts


theorem _root_.GlobalTheory.T.exists_holomorphicChart_of_expChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  first | exact @GlobalTheory.LieBase.exists_holoChart_of_expChart | exact GlobalTheory.LieBase.exists_holoChart_of_expChart | (intros; apply GlobalTheory.LieBase.exists_holoChart_of_expChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w (hw : w ∈ W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source)) => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.complexPoint_stalkFrame_vectors_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  first | exact @GlobalTheory.LieBase.frameAt_v_eq | exact GlobalTheory.LieBase.frameAt_v_eq | (intros; apply GlobalTheory.LieBase.frameAt_v_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  first | exact @GlobalTheory.LieBase.coords_eq_ratVal_of_chart | exact GlobalTheory.LieBase.coords_eq_ratVal_of_chart | (intros; apply GlobalTheory.LieBase.coords_eq_ratVal_of_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.hodgeMetric_uniformisation_smoothOn_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (hodgeMet Z U).SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} := by
  first | exact @GlobalTheory.LieBase.hodgeMet_smoothOn | exact GlobalTheory.LieBase.hodgeMet_smoothOn | (intros; apply GlobalTheory.LieBase.hodgeMet_smoothOn <;> assumption)
end
