module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleDescent

theorem isAmpleLB_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') [Flat (specOf g)]
    [Surjective (specOf g)] {X X' : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')} [UniversallyClosed f']
    (H : IsPullback π f' f (specOf g)) {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull π)) : IsAmpleLB L := by
  have hg : g.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (inferInstance : Flat (specOf g))
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨n, hn, s, hs, -⟩ := h.exists_affine z
  have hM := isLB_lbPow hL n
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hM π) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL π n).symm s
  obtain ⟨m, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have hz : IsUnit (gs (𝟙 X') z _ (σ.f fun _ => k)) :=
    (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => k) (mem_pull.2 hk)).1 (hσ.ge hs)
  rw [hu z k hk] at hz
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum hz
  refine ⟨n, hn, u j, (mem_nonzeroLocus_iff_pull (u j) π z hk).2 (isUnit_of_mul_isUnit_right hj), ?_⟩
  have ha := h.isAffineOpen_nonzeroLocus f' hn (secPowPull (u j) π)
  rw [nonzeroLocus_secPowPull] at ha
  have : IsAffine (π ⁻¹ᵁ nonzeroLocus (u j)) := ha
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict π (nonzeroLocus (u j))).paste_vert H)

theorem kTriv_of_pull {S S' : Scheme.{0}} [IsAffine S] [IsAffine S'] {f : S' ⟶ S} [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem proper_relAmple_kTriv_of_fieldExtension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [QuasiCompact G.hom] [IsSeparated G.hom] [Smooth G.hom] (G' : Over (Spec (CommRingCat.of K'))) [GrpObj G'] (Ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (specOf i) Ψ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (L.pull Ψ) → IsProper G'.hom → RelAmple G' L' → KTriv G' L' → IsProper G.hom ∧ RelAmple G L ∧ KTriv G L := by
  intro K K' _ _ i G _ _ _ _ G' _ Ψ h L L' hL hL' hw hP hA hK
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (specOf i) := inferInstance
  have : Surjective (specOf i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hG : IsProper G.hom := ⟨⟩
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  refine ⟨hG, (relAmple_iff_isAmpleLB_of_isAffine G hL).2 (isAmpleLB_of_pull i h.1 hL ?_),
    kTriv_of_pull h hL hL' hw hK⟩
  exact (isAmpleLB_of_relAmple_of_isAffine G' hL' hA).of_lbIso (LB.isLB_pull hL Ψ) hw.symm

end GlobalTheory.AmpleDescent
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.memKernelOfLineBundle_baseChange_representable : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  first | exact @GlobalTheory.memKL_baseChange_rep | exact GlobalTheory.memKL_baseChange_rep | (intros; apply GlobalTheory.memKL_baseChange_rep <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_unifPre_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (eA : (Over.pullback (jK R')).obj G' ≅ A'.A), IsMonHom eA.hom → (∃ wA : LB.Iso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen) → ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∃ (U' : UnifPre I' D' A' G') (wL' : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))), U'.LG = L' ∧ U'.gen = eA ∧ HEq wL' wL ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL' (r ≫ (fstG I' e G').left) z jL jL') := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hI hbc U eA heA hA L' wL he hwL hrig
  have hgp : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  obtain ⟨c', s', hs', hsr, Hc, Hs⟩ := cubical_symmetry_transport _ _ (specOf φ) G G' _ hgp U.LG L' wL he hwL hrig
    U.cubG U.symG U.symG_gen U.symG_rig
  choose h q' i' hh H using fun e => gtCoord_baseChange_maps R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
  choose gt' _ Hg using fun e => exists_gtCoord_pull hG R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
    (h e) (q' e) (i' e) (hh e) (H e)
  have C := fun e => gtCoord_compat_of_pull R R' φ D.toPre D'.toPre hD I I' G G' _ e (U.gt e) (U.gt (e + 1))
    (gt' e) (gt' (e + 1)) (h e) (h (e + 1)) (hh e) (hh (e + 1)) (Hg e) (Hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w' hw' sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.toPre.P.L D'.toPre.P.L U.LG.L L'.L
    D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB L'.isLB _ _ (U.gt e).pG.left (gt' e).pG.left (fstG I e G).left
    (fstG I' e G').left (h e) (Hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hwL (U.w_gen e)
  have RC := unifPull_rig_compat R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩)
  have Ev := pulled_comparison_even hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) s' hs' Hs
  have Cu := w_cub_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) hgp c' Hc
  have ext : LBIso (A'.L.pull eA.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB L'.isLB _) hA
      (LBIso.symm (LBIso.chartPull
        (Geo.Tor.chartPullPull L'.L _ _ rfl) (chartPullSame U.LG.L _ _ _ (pullback.fst G'.hom (jK R')) fun _ => rfl) ⟨wL, hwL⟩))
  exact ⟨{ smooth := MorphismProperty.of_isPullback hgp.1 U.smooth
           separated := MorphismProperty.of_isPullback hgp.1 U.separated
           gen := eA, gen_hom := heA, LG := L', cubG := c', symG := s', symG_gen := hs', symG_rig := hsr
           ext := ext, gt := gt', gt_q := fun e => (C e).1, gt_t := fun e => (C e).2
           w := w', w_gen := hw', w_rig := RC.1, w_even := Ev, w_cub := Cu, w_compat := RC.2 },
    wL, rfl, rfl, HEq.rfl, fun e => ⟨h e, hh e, Hg e, sq e⟩⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_iso_of_sectionRing_equiv_alt : ∀ (R : Type) [CommRing R] (X X' : Over (Spec (CommRingCat.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 L' n), (∀ j, d.f j = a.f j + resTop _ (scal X'.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)), (∀ j : Fin 1 → L'.ι, (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from d.f j) = (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from a.f j) * (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → (∃ (N : ℕ) (hN : 1 ≤ N) (κ : Type) (s : κ → H0 L' N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ (⨆ i, nonzeroLocus (θ N hN (s i)) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ IsAffineOpen (nonzeroLocus (θ N hN (s i)))) → ∃ Φ : X' ≅ X, (∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n), Φ.hom.left ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b ∧ ∀ (x : X'.left) (j : Fin 1 → L.ι) (j' : Fin 1 → L'.ι), x ∈ nonzeroLocus b → Φ.hom.left x ∈ L.U (j 0) → x ∈ L'.U (j' 0) → Geo.Tor.gs Φ.hom.left x _ ((θ n hn a).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (b.f j') = Geo.Tor.gs Φ.hom.left x _ ((θ n hn b).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (a.f j')) := by
  first | exact @GlobalTheory.exists_iso_of_sectionRing_equiv | exact GlobalTheory.exists_iso_of_sectionRing_equiv | (intros; apply GlobalTheory.exists_iso_of_sectionRing_equiv <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_nonzeroLocus_cover_affine (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) :
    (∀ x : P.A.left, ∃ s : H0 P.L N, x ∈ nonzeroLocus s) ∧ ∀ s : H0 P.L N, IsAffineOpen (nonzeroLocus s) := by
  classical
  have := P.isAb.proper
  let := P.grp
  obtain ⟨M, s, hs⟩ := AmpleSpan.exists_embedsBy_of_isPullback P.A P.isLB (hA S P N hN).2 (isAffineOpen_top S)
    (φ := 𝟙 P.A.left) (f' := P.A.hom) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  refine ⟨fun x => ?_, fun t => (hs.affine_and_surjective (t := s) (fun j => ⟨Pi.single j 1, fun k => ?_⟩) t).1⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.1.ge (Set.mem_univ x))
    exact ⟨s i, hi⟩
  · rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, map_one, _root_.one_mul]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem exists_iso_of_polAV_sectionRing : Laws → ∀ (K : Type) [Field K] (P P' : PolAV (Spec (CommRingCat.of K))), ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 P'.L n), (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)), (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from d.f j) = (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from a.f j) * (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from b.f j)) → ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ n hn a).f j) * (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : P'.A ≅ P.A, ∃ w : LB.Iso P'.L (P.L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (p : Fin 1 → P.L.ι) (q : Fin 1 → P'.L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z)) ∈ P.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z) ∈ P'.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 P'.A.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) q) ((a).f q)) := by
  intro hL K _ P P' θ hlin hmul
  have := P.isAb.proper
  have := P'.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace P'.A.left := QuasiCompact.compactSpace_of_compactSpace P'.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  have : QuasiSeparatedSpace P'.A.left := quasiSeparatedSpace_of_quasiSeparated P'.A.hom
  obtain ⟨c, a⟩ := polAV_nonzeroLocus_cover_affine hL.ample P (le_refl 4)
  obtain ⟨c', a'⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (le_refl 4)
  obtain ⟨c₅, -⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (N := 4 + 1) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, by norm_num, H0 P'.L 4, id, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (c' x),
      top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (by
        obtain ⟨s, hs⟩ := c x
        obtain ⟨t, rfl⟩ := (θ 4 (by norm_num)).surjective s
        exact ⟨t, hs⟩), fun i => ⟨a' _, a _⟩⟩
  refine ⟨Φ, exists_iso_of_sectionRing K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Φ.hom.left hΦ fun x => ?_⟩
  obtain ⟨s, hs⟩ := c' x
  obtain ⟨t, ht⟩ := c₅ x
  exact ⟨4, by norm_num, s, t, hs, ht⟩

end GlobalTheory
end
end
