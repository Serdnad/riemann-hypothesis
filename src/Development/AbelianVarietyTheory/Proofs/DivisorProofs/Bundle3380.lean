module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle141
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_lift_id {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : 𝟙 X ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R))) :
    IsClosedImmersion (pullback.lift (𝟙 X) f h) := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]
    infer_instance
  have e : pullback.lift (𝟙 X) f h = inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id R)))) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  rw [e]
  infer_instance

theorem veryAmpleBy_of_lbIso {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H H'' : LB X} (hH : H.IsLB) (hH'' : H''.IsLB) (hI : LBIso H H'') {n : ℕ} {s : Fin (n + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ s'' : Fin (n + 1) → LB.Sec H'', VeryAmpleBy f H'' s'' := by
  obtain ⟨w, hw⟩ := LBIso.trans hH'' hH (pull_isLB hH _) (LBIso.symm hI) (LBIso.symm (GlobalTheory.lbIso_pull_id hH))
  choose s'' hs'' using fun j => (GlobalTheory.SecPullIso.section_pull X X (𝟙 X) H H'' w hH hH'' hw (s j)).1.exists
  exact ⟨s'', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R (RingHom.id R) X f (𝟙 X)
    (by rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]; simp)
    (isClosedImmersion_lift_id f _) H'' w s'' hH'' hw fun j => hs'' j⟩

end GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem formalAlgebraisation_schemes : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro R _ _ I hI Y β hβ hY N hN hNN hA
  choose v hv using hNN
  obtain ⟨a, ha1, hlift⟩ := GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower R I Y β hβ N hN hA
  have hpw : ∀ (c : ℤ) (e : ℕ), ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
      wa.IsGen ∧ ∀ (z : (Y e).left) (k : (N (e + 1)).ι) (k' : (N e).ι), β e z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        Geo.Tor.gw wa (𝟙 _) z k k' = Geo.Tor.gw (v e) (𝟙 _) z k k' ^ c := fun c e => by
    obtain ⟨wa, h1, h2⟩ := GlobalTheory.T.exists_bundleIso_zpow_local_units_pow (Y (e + 1)).left (Y e).left (β e) (N (e + 1)) (N e) (v e) (hv e) c
    exact ⟨wa, h1, fun z k k' hk hk' => h2 (Y e).left (𝟙 _) z k k' hk hk'⟩
  choose va hva hvaw using hpw (a : ℤ)
  choose vb hvb hvbw using hpw ((a + 1 : ℕ) : ℤ)
  obtain ⟨n, s, hsRel, hsVA⟩ := hlift a (Or.inl rfl) va hva
  obtain ⟨n₂, s₂, hs₂Rel, hs₂VA⟩ := hlift (a + 1) (Or.inr rfl) vb hvb
  obtain ⟨B, H', s', b, w, hH', hVA', hpb, hcomp, hw, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hI Y β hβ
    (fun e => GlobalTheory.AbLaw.pw (N e) a) va (fun e => ⟨isLB_pw (hN e) _, hva e⟩) n s hsRel (hsVA 0)
  have hBp : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R B.left B.hom ⟨H', hH', n, s', hVA'⟩
  obtain ⟨M₂, s₂', w', hM₂, hw'⟩ := GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem R I hI B hBp Y β b hpb hcomp
    (fun e => GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) vb (fun e => ⟨isLB_pw (hN e) _, hvb e⟩) n₂ s₂ hs₂Rel
    (fun e => (hs₂VA e).1)
  have c1 : ∀ e z k l' l, b e z ∈ H'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ (a : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvaw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) H'
      (GlobalTheory.AbLaw.pw (N (e + 1)) a) (GlobalTheory.AbLaw.pw (N e) a) (w (e + 1)) (va e) (w e) (Fin (n + 1)) s' (s (e + 1)) (s e)
      (fun j => (hw (e + 1)).2 j) (fun j => hsRel e j) (fun j => (hw e).2 j) (hsVA e).1 z k l' l h1 h2 h3
  have c2 : ∀ e z k l' l, b e z ∈ M₂.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w' e) (𝟙 _) z k l =
        Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ ((a + 1 : ℕ) : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvbw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) M₂
      (GlobalTheory.AbLaw.pw (N (e + 1)) ((a + 1 : ℕ) : ℤ)) (GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) (w' (e + 1)) (vb e) (w' e)
      (Fin (n₂ + 1)) s₂' (s₂ (e + 1)) (s₂ e)
      (fun j => (hw' (e + 1)).2 j) (fun j => hs₂Rel e j) (fun j => (hw' e).2 j) (hs₂VA e).1 z k l' l h1 h2 h3
  have hiso := GlobalTheory.T.lineBundleIso_algebraised_powers_compatible R I hI B hBp Y β b hpb hcomp N v hN (a : ℤ) ((a + 1 : ℕ) : ℤ) H' M₂ hH' hM₂ w w'
    (fun e => ⟨(hw e).1, (hw' e).1⟩) c1 c2
  have hcast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; rfl
  rw [hcast] at hiso
  have hM : (GlobalTheory.AbLaw.tw M₂ H' (-1)).IsLB := isLB_tw hM₂ hH' _
  have hH'M : LBIso H' (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M₂ H' (-1)) a) := GlobalTheory.T.cancel_powers_of_cech_line_bundles.2 B.left H' M₂ a hH' hM₂ hiso
  have hNM : ∀ e, LBIso (N e) ((GlobalTheory.AbLaw.tw M₂ H' (-1)).pull (b e)) := fun e =>
    GlobalTheory.T.cancel_powers_of_cech_line_bundles.1 B.left (Y e).left (b e) H' M₂ (N e) a hH' hM₂ (hN e) ⟨w e, (hw e).1⟩
      (hcast ▸ ⟨w' e, (hw' e).1⟩)
  obtain ⟨s'', hs''⟩ := veryAmpleBy_of_lbIso B.hom hH' (isLB_pw hM _) hH'M hVA'
  exact ⟨B, GlobalTheory.AbLaw.tw M₂ H' (-1), b, hBp, hM,
    (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B _ hM).2 ⟨a, ha1, n, s'', hs''⟩, hpb, hcomp, hNM⟩

end GlobalTheory.FormalAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidRoot

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem pow_comp_hom {Z H : Over S} [GrpObj H] (f : A ⟶ H) [IsMonHom f] (x : Z ⟶ A) (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pull_eq_evc {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S} (w : Y ⟶ A ⊗ A) :
    CechPic.pull w.left (cls P hP) = evc hP (w ≫ fst A A) (w ≫ snd A A) := by
  rw [evc, lift_comp_fst_snd]

theorem cube_rel (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S}
    (x y z : Y ⟶ A ⊗ A) :
    CechPic.pull (x * y * z).left (cls P hP) - CechPic.pull (x * y).left (cls P hP)
      - CechPic.pull (x * z).left (cls P hP) - CechPic.pull (y * z).left (cls P hP)
      + CechPic.pull x.left (cls P hP) + CechPic.pull y.left (cls P hP) + CechPic.pull z.left (cls P hP)
      - CechPic.pull (1 : Y ⟶ A ⊗ A).left (cls P hP) = 0 := by
  have hX := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have t := GlobalTheory.CubeTop.cubeTheorem S (A ⊗ A) hX P hP Y x y z
  have z0 := (cls_linComb hP _ _ (LB.isLB_linComb hP _ _)).symm.trans
    ((cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 t)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_zsmul, neg_one_zsmul, add_zero] at z0
  rw [← z0]
  abel

theorem additive_of_birigid (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ A))) :
    IsAdditive P ∧ IsAdditive (swap P) := by
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := cube_rel hA hP (lift a 1) (lift a' 1) (lift 1 t)
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_rel hA hP (lift a 1) (lift 1 t) (lift 1 t')
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.BirigidRoot

theorem GlobalTheory.BirigidRoot.iso_of_lbPow_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ)
    (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB →
    (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB →
    (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) →
    LBIso P₁ P₂ := by
  intro S A _ _ k P₁ P₂ hA hk _ hP₁ h₁ h₂ hP₂ h₁' h₂' e
  obtain ⟨a₁, b₁⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₁ h₁ h₂
  obtain ⟨a₂, b₂⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₂ h₁' h₂'
  obtain ⟨D, _, Q, -, -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x₁, hx₁, ex₁⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₁ a₁ b₁
  obtain ⟨x₂, hx₂, ex₂⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₂ a₂ b₂
  have hk' : k • cls P₁ hP₁ = k • cls P₂ hP₂ := by
    rw [← cls_lbPow hP₁ k (LB.isLB_linComb hP₁ _ _), ← cls_lbPow hP₂ k (LB.isLB_linComb hP₂ _ _)]
    exact (cls_eq_iff _ _).2 e
  have pw : ∀ (y : A ⟶ D) (n : ℕ), evc q.isLB (fst A A) (snd A A ≫ y ^ n) =
      n • evc q.isLB (fst A A) (snd A A ≫ y) := by
    intro y n
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul]; exact evc_one_right q.isLB q.zero _
    | succ n ih =>
      rw [pow_succ, MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff q.isLB).1 q'.additive, ih, succ_nsmul]
  have hpow : x₁ ^ k = x₂ ^ k := GlobalTheory.BirigidLift.dual_ext q (by rw [pw, pw, ← ex₁, ← ex₂, hk'])
  have hx : x₁ = x₂ := by
    obtain ⟨hfl, hsu, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
    have c : (((𝟙 A) ^ k) ≫ x₁).left = (((𝟙 A) ^ k) ≫ x₂).left := by
      rw [GlobalTheory.BirigidRoot.pow_comp_hom, GlobalTheory.BirigidRoot.pow_comp_hom, Category.id_comp, Category.id_comp, hpow]
    rw [Over.comp_left, Over.comp_left] at c
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 A) ^ k).left).1 c)
  subst hx
  exact (cls_eq_iff hP₁ hP₂).1 (ex₁.trans ex₂.symm)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.stein_factorisation_connected_fibres : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  first | exact @GlobalTheory.SteinFact.stein_factorisation | exact GlobalTheory.SteinFact.stein_factorisation | (intros; apply GlobalTheory.SteinFact.stein_factorisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | exact GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbLocusProperNormal

theorem isProper_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth (Sp V) G
  have p : Sp (ResidueField V) := IsLocalRing.closedPoint (ResidueField V)
  refine GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr V G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance ?_
  exact GlobalTheory.AbelianTrait.isProper_snd_of_mem_abLocus G (K := ResidueField V)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) p (by rw [hab]; trivial)

theorem isProper_of_abLocus_eq_univ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  haveI : IsSemiAbelian G := hG
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.smooth
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R G.left G.hom ?_
  intro V K _ _ _ _ _ _ _ x y _ hxy
  have hGV : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have habV : abLocus ((Over.pullback y).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom y) z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper (pullback.snd G.hom y) := isProper_dvr V _ hGV habV
  let xV : Sp K ⟶ pullback G.hom y := pullback.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence (pullback.snd G.hom y) := by
    have h : UniversallyClosed (pullback.snd G.hom y) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq (pullback.snd G.hom y) :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact pullback.lift_snd _ _ _⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ pullback.fst G.hom y, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact pullback.lift_fst _ _ _

theorem isProper_restrict_of_subset_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  intro R _ _ _ _ G _ hG W hW
  let I := {r : R // r ≠ 0 ∧ ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) : Set (Sp R)) ⊆ (W : Set (Sp R))}
  let t : ∀ i : I, Sp (Localization.Away i.1) ⟶ Sp R := fun i => spMap (algebraMap R (Localization.Away i.1))
  have hrange : ∀ i : I, Set.range (t i) = (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)) := fun i =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away i.1) i.1
  have hprop : ∀ i : I, IsProper (pullback.snd G.hom (t i) ∣_ ⊤) := by
    intro i
    haveI : IsDomain (Localization.Away i.1) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors i.2.1)
    haveI : IsNoetherianRing (Localization.Away i.1) :=
      IsLocalization.isNoetherianRing (Submonoid.powers i.1) _ inferInstance
    have hGi : IsSemiAbelian ((Over.pullback (t i)).obj G) := IsSemiAbelian.pullback (t i) G hG
    have hab : abLocus ((Over.pullback (t i)).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
      (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (t i)) z).1
        (hW (i.2.2 (by rw [← hrange i]; exact ⟨z, rfl⟩)))
    have : IsProper (pullback.snd G.hom (t i)) := isProper_of_abLocus_eq_univ _ _ hGi hab
    infer_instance
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom t (fun i => pullback.snd G.hom (t i))
    (fun i => pullback.fst G.hom (t i)) (fun i => IsPullback.of_hasPullback G.hom (t i)) (fun _ => ⊤) hprop W
    (fun i => ?_) (fun z hz => ?_)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine i.2.2 ?_
    rw [← hrange i]
    exact ⟨_, rfl⟩
  · obtain ⟨_, ⟨r, rfl⟩, hzr, hrW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr : r ≠ 0 := fun h0 => hzr (by rw [h0]; exact zero_mem _)
    let i : I := ⟨r, hr, hrW⟩
    obtain ⟨y, hy⟩ : z ∈ Set.range (t i) := by rw [hrange i]; exact hzr
    exact ⟨i, ⟨y, trivial⟩, by first | exact hy | (erw [Scheme.Hom.comp_apply]; exact hy) | simpa using hy⟩

end GlobalTheory.AbLocusProperNormal
end
