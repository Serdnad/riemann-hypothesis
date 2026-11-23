module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTermBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle180
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ExtensionMul

section General

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem exists_isPullback_pow [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P P' Q : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q)
    {p : P' ⟶ P} {y : P' ⟶ G} (hP' : IsPullback y p q b)
    {s : Q ⟶ P'} {r : Q ⟶ G} (hQ : IsPullback s r p φ) :
    ∃ (c : P' ⟶ T) (t : Q ⟶ T), IsPullback s t c ((𝟙 T) ^ N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  obtain ⟨c, hc⟩ := ex ((p ≫ a) / y ^ N) (by
    rw [GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow,
      Category.comp_id, div_self'])
  have hsr : s ≫ y ≫ q = r ≫ q := by
    rw [hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]
  have hsa : s ≫ p ≫ a = r ^ N := by
    rw [← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]
  obtain ⟨t, ht⟩ := ex (r / (s ≫ y)) (by
    rw [GrpObj.div_comp, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, MonObj.comp_pow, Category.comp_id]
    have hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow,
          ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]
      · rw [Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq,
          MonObj.comp_one, _root_.one_mul, hP'.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      rw [hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]

theorem of_pow_kernel (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q) (h : Pr ((𝟙 T) ^ N : T ⟶ T).left) :
    Pr φ.left := by
  have hP' := IsPullback.of_hasPullback q b
  have hQ := IsPullback.of_hasPullback (pullback.snd q b) φ
  obtain ⟨c, t, H⟩ := exists_isPullback_pow i q hk N hP hφa hφb hP' hQ
  have hP'' := hP'.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end General

theorem pow_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : E.IsGt G)
    (N : ℕ) (hN : 1 ≤ N) (h1 : IsFinite ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) (h2 : Flat ((𝟙 E.B) ^ N : E.B ⟶ E.B).left)
    (h3 : Surjective ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) :
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left ∧ Flat ((𝟙 G) ^ N : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ N : G ⟶ G).left := by
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have hs : Surjective (mulN (splitTorus S E.X) N).left := Diag.surjective_mulN S E.X hN'
  rw [MulEtaleDvr.mulN_eq_pow] at hf hl hs
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a0 : Surjective (hP.lift _ _ w).left := of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs
  have a1 : Flat (hP.lift _ _ w).left := of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget S)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  have b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @Flat) hP' h2
  have b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hP' h3
  rw [← ha, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem exists_represents_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ ∧ Smooth Gt.hom ∧ IsSeparated Gt.hom ∧ ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left := by
  intro R _ _ _ D
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := TorusModel.exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ,
    (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩
  · obtain ⟨d⟩ := hH
    have := d.q_affine
    have := (TorusModel.splitExt D).isAbelian.proper
    rw [← Over.w d.q]
    infer_instance
  · obtain ⟨h₁, h₂, h₃, -⟩ := hL.mulN _ D.P k hk
    exact pow_of_isGt _ H hH k hk h₁ h₂ h₃

end GlobalTheory.ExtensionMul
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsionFormCompare


open UnifBaseChange ExpandsLinear in
theorem exists_unif_pull_of_deg (hP : PolBaseChangeSt) (hG : GlobalFnsSt) (hS : SecBaseChangeSt)
    (hT : DVR.TwistBaseChangeStatement)
    (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R') (hR : AdmBase R I) (hR' : AdmBase R' I') (φ : R →+* R') (hI : I.map φ ≤ I')
    (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (hsa : IsSemiAbelian G)
    (U : Unif I D A G) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (hgD : D'.toPre.P.g = D.toPre.P.g)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (hg : A'.g = A.g)
    (eA : (Over.pullback (jK R')).obj G' ≅ A'.A) (heA : IsMonHom eA.hom)
    (hwA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen)
    (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))))
    (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G)
    (hwL : wL.IsGen)
    (hrig : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig)) :
    ∃ U' : Unif I' D' A' G', U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnif φ hD bc U U' := by
  obtain ⟨U', wL', hL, hgen, hw, hlev⟩ := exists_unifPre_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc
    U.toUnifPre eA heA hwA L' wL he hwL hrig
  subst hL
  obtain rfl := eq_of_heq hw
  haveI := hsa.geomConnected
  haveI := hsa.quasiCompact
  haveI : GeometricallyConnected G'.hom := by
    rw [← Over.w bc.hom]
    have : IsIso bc.hom.left := ((Over.forget _).mapIso bc).isIso_hom
    have : GeometricallyConnected ((Over.pullback (specOf φ)).obj G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (specOf φ)))
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := bc.hom.left) (f := ((Over.pullback (specOf φ)).obj G).hom) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) this
  haveI := hR.1
  haveI := hR'.1
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨-, hd⟩ := FamDim.finrank_fam hG hP hT R D.toPre D.tau_bimult (psiOnExists R I hR D) (FractionRing R) k hk
    obtain ⟨hfin, hd'⟩ := FamDim.finrank_fam hG hP hT R' D'.toPre D'.tau_bimult (psiOnExists R' I' hR' D')
      (FractionRing R') k hk
    have hdA := finrank_fam_of_expBij hS R I hR D A G U.toUnifPre k hk (U.expand k hk)
    have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
    refine ExpansionCriterion.expBij_of_onto hS R' I' hR' D' A' G' U' k hk hfin (by rw [hd', hrk, hgD, ← hd, hdA, hg]) fun F₀ => ?_
    obtain ⟨n, F, f, F', f', hF, hspan⟩ := T.exists_integral_families_span_pullDegeneration hP hG hT R R' I hR φ D D'.toPre hD k hk
    have hb : ∀ i, ∃ b : U'.SecK k, U'.Expands k b (F' i) := by
      intro i
      obtain ⟨σ, hσ⟩ := exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k (fun F => ((U.expand k hk).2 F).exists) (F i) (f i)
        (hF i).1
      obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL' hwL
        (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
        (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
      obtain ⟨b, hb⟩ := exists_secScal_one U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))
        (pullback.fst G'.hom (jK R')) (fun _ => pullback.fst G'.hom (jK R'))
        (funext fun _ => (Category.comp_id _).symm) σ'
      refine ⟨b, 1, one_ne_zero, σ', f' i, by rw [scal_one]; exact hb,
        fun α => by rw [scal_one]; exact (hF i).2.1 α, fun e => ?_⟩
      obtain ⟨h, hh⟩ := hlev e
      exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U' _ hD.w hD.xe _ wL' hD.w_gen hwL
        (ExpGTrans.famφB_pull hD) e e k h ⟨hh.1, hh.2⟩ σ σ' (f i) (f' i) hσ' (hF i).2.2 (hσ e)
    choose b hb using hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan ▸ Submodule.mem_top : F₀ ∈ _)
    exact ⟨secComb (fun i => scal (pullback.snd G'.hom (jK R')) (c i)) b,
      expands_linear R' I' hR' D' A' G' U' k n b F' c _ hb fun _ => rfl⟩
  exact ⟨⟨U', hexp⟩, rfl, hgen,
    (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U ⟨U', hexp⟩).2 ⟨wL', hwL, he, hrig, hlev⟩⟩

theorem RigAlong.read {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {ε : G' ⟶ G} [IsMonHom ε] {L : RigLB G} {L' : RigLB G'} {w : LB.Iso L'.L (L.L.pull ε.left)}
    (h : RigAlong ε L L' w) {F : G'.left ⟶ G.left} (hF : F = ε.left) {e : S ⟶ S} (he₀ : e = 𝟙 S) :
    ∃ (wL : LB.Iso L'.L (L.L.pull F)) (he : eSec G' ≫ F = e ≫ eSec G), wL.IsGen ∧
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf F e he L.L L.rig) := by
  subst hF he₀
  have he : eSec G' ≫ ε.left = 𝟙 S ≫ eSec G := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε)
  exact ⟨w, he, h.1, (maps_iff _ _ (fun _ => eSec G) _ L'.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L)
    (fun _ => rfl)).2 h.2⟩

theorem exists_unif_move : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G), AdmBase R I → IsSemiAbelian G → IsMonHom ε.hom → ∀ (U : Unif I D A G) (L' : RigLB G') (w : LB.Iso L'.L (U.LG.L.pull ε.hom.left)), RigAlong ε.hom U.LG L' w → ∀ hD : IsPullDeg (RingHom.id R) D.toPre D.toPre, ∃ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U' : Unif I D A G'), IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left ∧ U'.LG = L' ∧ U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro R _ _ I D A G G' _ _ _ _ ε hR hsa hε U L' w hw hD
  have hs := specOf_id R
  have gp₁ : IsGrpPullback G' G (specOf (RingHom.id R)) ε.hom.left :=
    (isGrpPullback_of_iso ε).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have := U.gen_hom
  let eA : (Over.pullback (jK R)).obj G' ≅ A.A := (Over.pullback (jK R)).mapIso ε ≪≫ U.gen
  have mE : IsMonHom eA.hom := by
    show IsMonHom ((Over.pullback (jK R)).map ε.hom ≫ U.gen.hom)
    infer_instance
  have wA : LBIso (A.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := ((Over.pullback (jK R)).map ε.hom).left)
      (chartPullSame A.L (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => rfl)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => by
        rw [hbc]; exact (pullback.lift_fst _ _ _).symm) U.ext
  obtain ⟨wL, he, gL, rL⟩ := hw.read hbc hs
  obtain ⟨U', hL, hgen, hPU⟩ := exists_unif_pull_of_deg GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R I I hR hR (RingHom.id R) (by rw [Ideal.map_id]) D A G hsa U D hD rfl G' bc mbc A rfl eA mE wA L' wL he gL rL
  exact ⟨bc, U', mbc, hbc, hL, by rw [hgen]; rfl, hPU⟩

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.BuildAdd

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem exists_add_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.cutBy_graph_addition hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ hDen hFam hSm => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hPR, hp⟩, -, hfib⟩ := hFam
  obtain ⟨I₂, M₂, th₂, hPR₂, hseg⟩ :=
    GlobalTheory.SegreCoord.exists_segre_coordinates R (Ix g ((n ^ j) ^ 2)) I Z M th hPR
  have hP1 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR).2.1
  have hP2 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR₂).2.1
  have hS2 : Smooth (Z ⊗ Z).hom := by
    have := hSm
    rw [Over.tensorObj_hom]
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x φ => ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s)
      (ψ : t.A.left ⟶ Z.left) (e : (t.A ⊗ t.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)), IsIso e ∧
      Good b Mat κ β v x t ∧ Fib (n ^ 2) M th sc x t ψ ∧ IsSquare ψ (e ≫ pullback.fst _ _) ∧
      e ≫ pullback.snd _ _ = (t.A ⊗ t.A).hom ∧ e ≫ φ = (μ[t.A]).left ≫ ψ
  have mk : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o)
      (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left), Good b Mat κ β v x t →
      Fib (n ^ 2) M th sc x t ψ → ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare ψ φ₂ → ∃ φ, G K x φ := by
    intro K _ _ x s t ψ hG hF φ₂ hsq
    have hpb := GlobalTheory.ZM.BuildAdd.isPullback_square hF.1 φ₂ hsq
    refine ⟨hpb.isoPullback.inv ≫ (μ[t.A]).left ≫ ψ, inferInstance, s, t, ψ, hpb.isoPullback.hom, inferInstance, hG, hF, ?_,
      hpb.isoPullback_hom_snd, by simp⟩
    rw [hpb.isoPullback_hom_fst]
    exact hsq
  have hGprop : ∀ (K : Type) [Field K] (x : R →+* K) (φ : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left), G K x φ →
      φ ≫ Z.hom = pullback.snd _ _ ≫ spMap x ∧
      CutBy (graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th φ) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (i : (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2)) =>
          x ((p h.1 i.1.1 * p h.2 i.1.2) * p (h.1 + h.2) i.2)) := by
    intro K _ x φ hφ
    obtain ⟨_, s, t, ψ, e, _, hG, hF, hsq, hsn, heφ⟩ := hφ
    have hw : ψ ≫ Z.hom = t.A.hom ≫ spMap x := hF.1.w
    refine ⟨?_, ?_⟩
    · rw [← cancel_epi e, reassoc_of% heφ, reassoc_of% hsn, hw, ← Category.assoc, Over.w]
    have hs : s = spMap (x.comp β) := hG.1.trans (spMap_comp x β).symm
    subst hs
    obtain ⟨-, ⟨σ, hEmb, hσ⟩, -, hlab⟩ := hF
    obtain ⟨N₂, t₂, hN₂, hseg₂, heq⟩ :=
      GlobalTheory.ZM.BuildAdd.graph_transport x Z M th M₂ th₂ hPR₂.1 hseg t.A ψ _ σ hσ e hsq hsn φ heφ
    rw [← heq]
    have hl : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      rw [hσ, ← Category.assoc, ← Over.comp_left, lift_snd, hlab h]
      have hx : (sc h).left ≫ Z.hom = spMap (RingHom.id R) := by
        rw [Over.w]
        simp [Out.baseOver, spMap]
      have hu := (hPR.2.1 R (RingHom.id R) (sc h).left (p h) hx (hp h)).1
      exact GlobalTheory.SegreCoord.secCoord_of_loc (GlobalTheory.SegreCoord.unimod_map hu x)
        ((GlobalTheory.SegreCoord.loc_of_secCoord (hp h)).baseChange x)
    have := hQ K (x.comp β) t σ (fun h a => x (p h a)) N₂ t₂ hN₂ hEmb hseg₂ hl
    simp only [map_mul]
    exact this
  have hDense : DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} := by
    intro f hf
    apply hDen.1 f
    intro q hq hqp
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    have hG : Good b Mat κ β v x t := ⟨rfl, hsh, hth⟩
    obtain ⟨ψ, hψ⟩ := hfib K x _ t hG
    obtain ⟨φ₂, hsq⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ.1.w
    obtain ⟨φ, hφ⟩ := mk K x _ t ψ hG hψ φ₂ hsq
    exact hf q ⟨K, inferInstance, x, φ, hker, hφ⟩ hqp
  obtain ⟨K₀, _, _, x₀, t₀, hker₀, hsh₀, hth₀⟩ := hDen.2
  have hG₀ : Good b Mat κ β v x₀ t₀ := ⟨rfl, hsh₀, hth₀⟩
  obtain ⟨ψ₀, hψ₀⟩ := hfib K₀ x₀ _ t₀ hG₀
  obtain ⟨φ₂₀, hsq₀⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ₀.1.w
  obtain ⟨φ₀, hφ₀⟩ := mk K₀ x₀ _ t₀ ψ₀ hG₀ hψ₀ φ₂₀ hsq₀
  obtain ⟨f, hf0, H⟩ := GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit R
    (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2))
    (Z ⊗ Z) Z I₂ I M₂ M th₂ th (fun h i => p h.1 i.1 * p h.2 i.2) (fun h c => p (h.1 + h.2) c) Q d G
    hPR₂ hPR hP2 hP1 hS2 hGprop hDense K₀ x₀ φ₀ hφ₀
  refine ⟨f, fun hf => hf0 ?_, ?_⟩
  · rw [← hker₀] at hf
    exact RingHom.mem_ker.mp hf
  intro R' _ ρ hu Z' π hπ
  obtain ⟨π₂, hsqπ⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hπ.w
  have hpbπ := GlobalTheory.ZM.BuildAdd.isPullback_square hπ π₂ hsqπ
  obtain ⟨F, hF, hU⟩ := H R' ρ hu (Z' ⊗ Z').left π₂ (Z' ⊗ Z').hom hpbπ.w
  refine ⟨Over.homMk (hπ.lift F (Z' ⊗ Z').hom hF) (hπ.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ hG hFib hφw φ₂ hsq
  have hpb1 : IsPullback φ t.A.hom Z'.hom (spMap x) := by
    refine IsPullback.of_right ?_ hφw hπ
    rw [← spMap_comp]
    exact hFib.1
  have hpb2 := GlobalTheory.ZM.BuildAdd.isPullback_square hpb1 φ₂ hsq
  have hsq' : IsSquare (φ ≫ π) (φ₂ ≫ π₂) := by
    constructor
    · rw [Category.assoc, hsqπ.1, reassoc_of% hsq.1]
    · rw [Category.assoc, hsqπ.2, reassoc_of% hsq.2]
  have hpb3 := GlobalTheory.ZM.BuildAdd.isPullback_square hFib.1 (φ₂ ≫ π₂) hsq'
  have hGφ : G K (x.comp ρ) (hpb3.isoPullback.inv ≫ (μ[t.A]).left ≫ φ ≫ π) :=
    ⟨inferInstance, s, t, φ ≫ π, hpb3.isoPullback.hom, inferInstance, hG, hFib,
      by rw [hpb3.isoPullback_hom_fst]; exact hsq', hpb3.isoPullback_hom_snd, by simp⟩
  have key := hU K (x.comp ρ) _ hGφ (hpb3.isoPullback.inv ≫ φ₂)
    (by rw [Category.assoc]; exact hpb3.isoPullback_inv_fst)
  rw [Category.assoc, cancel_epi] at key
  show φ₂ ≫ hπ.lift F (Z' ⊗ Z').hom hF = (μ[t.A]).left ≫ φ
  apply hπ.hom_ext
  · rw [Category.assoc, hπ.lift_fst, Category.assoc]
    exact key.symm
  · rw [Category.assoc, hπ.lift_snd, Category.assoc, hφw, ← Category.assoc, Over.w]
    exact hpb2.w

end GlobalTheory.ZM.NearBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.closing_of_abelianSchemeLaws : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1c :=
  _root_.GlobalTheory.familyUnif_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end
