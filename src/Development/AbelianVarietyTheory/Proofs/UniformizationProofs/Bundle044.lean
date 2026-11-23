module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionSingleValued

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep

theorem exists_indep_coords (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] [Algebra R F] [IsScalarTower R (FractionRing R) F] {Λ : Type} [Fintype Λ] (c : Λ → F) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → F) (a : Λ → κ → R), LinearIndependent R b ∧ ∀ i, c i = ∑ l, a i l • b l := by
  classical
  let B := Module.Basis.ofVectorSpace (FractionRing R) F
  let S := Finset.univ.biUnion fun i => (B.repr (c i)).support
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Λ × S => B.repr (c p.1) p.2)
  choose a ha using hd
  have hd0 : algebraMap R (FractionRing R) d ≠ 0 := (IsLocalization.map_units _ d).ne_zero
  refine ⟨S, inferInstance, fun l => (algebraMap R (FractionRing R) d)⁻¹ • B l, fun i l => a (i, l), ?_, fun i => ?_⟩
  · refine LinearIndependent.restrict_scalars' (K := FractionRing R) R ?_
    exact (B.linearIndependent.comp (fun l : S => l.1) Subtype.val_injective).units_smul
      (fun _ => (Units.mk0 _ hd0)⁻¹)
  · have h : ∀ l : S, a (i, l) • (algebraMap R (FractionRing R) d)⁻¹ • B l = B.repr (c i) l • B l := fun l => by
      rw [← algebraMap_smul (FractionRing R), ha, smul_smul, Algebra.smul_def (d : R), mul_right_comm,
        mul_inv_cancel₀ hd0, _root_.one_mul]
    simp only [h]
    rw [Finset.sum_coe_sort S (fun l => B.repr (c i) l • B l)]
    conv_lhs => rw [← B.linearCombination_repr (c i), Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (B.repr (c i)).support) (Finset.mem_univ i)) _
      (fun _ _ => zero_smul _ _)

theorem flat_germOf {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) :
    (germOf p x).Flat := by
  have e : germOf p x = (p.stalkMap x).hom.comp
      (((Sp R).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.ext fun c => by
      rw [germOf_apply, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  rw [e]
  refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) ?_) (Flat.stalkMap p x)
  have hU := isAffineOpen_top (Sp R)
  let _ := (Sp R).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
  have := hU.isLocalization_stalk ⟨p x, trivial⟩
  exact IsLocalization.flat ((Sp R).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp R).Opens)) : Sp R))
    (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl

theorem split_relation {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) {U : X.Opens} (hx : x ∈ U) {Λ κ : Type} [Fintype Λ] [Fintype κ]
    (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R) (s : Λ → Γ(X, U))
    (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ z, r z ∈ U →
        ∑ i, germOf q z (∑ l, a i l • b l) * gs r z U (s i) = 0) (l : κ) :
    ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i) = 0 := by
  let O : Type := X.presheaf.stalk x
  let : Algebra R O := (germOf p x).toAlgebra
  have : Module.Flat R O := flat_germOf p x
  have hi : LinearIndependent O (fun l => (1 : O) ⊗ₜ[R] b l) := Module.Flat.linearIndependent_one_tmul hb
  refine Fintype.linearIndependent_iff.1 hi (fun l => ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) ?_ l
  let eL : O →+* TensorProduct R O F := Algebra.TensorProduct.includeLeftRingHom
  let eR : F →+* TensorProduct R O F := (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := F)).toRingHom
  refine eq_zero_of_germOf (B := CommRingCat.of (TensorProduct R O F)) _ fun z => ?_
  have h := H (Spec (CommRingCat.of (TensorProduct R O F))) (Spec.map (CommRingCat.ofHom eR))
    ((Spec.map (CommRingCat.ofHom eL) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x) (by
      rw [Category.assoc, fromSpecStalk_comp]
      refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
      ext r
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := O) (B := F) r)) z (fromSpecStalk_mem x hx _)
  have e : ∑ l, (∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) • ((1 : O) ⊗ₜ[R] b l) =
      ∑ i, eR (∑ l, a i l • b l) * eL (gs (𝟙 X) x U (s i)) := by

    simp only [Finset.sum_smul, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    show _ = ((1 : O) ⊗ₜ[R] (a i l • b l)) * ((gs (𝟙 X) x U (s i) : O) ⊗ₜ[R] (1 : F))
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rfl

  rw [e, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
  · rw [gs_fromSpecStalk x hx]
    exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom eL) z _).symm

theorem gs_scal {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    (a : R) : gs r z ⊤ (scal p a) = germOf (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (germOf_apply _ _ _).symm

theorem gs_scal_comb {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    {U : X.Opens} (hz : r z ∈ U) {Λ : Type} [Fintype Λ] (a : Λ → R) (s : Λ → Γ(X, U)) :
    gs r z U (∑ i, resTop U (scal p (a i)) * s i) = ∑ i, germOf (r ≫ p) z (a i) * gs r z U (s i) := by
  rw [gs_fsum r z U hz]
  exact Finset.sum_congr rfl fun i _ => by rw [gs_mul r z U hz, gs_res r z le_top hz, gs_scal]

theorem sum_append {F O T : Type} [CommRing F] [CommRing O] (g : F →+* O) {n n' : ℕ} (c : Fin n → F) (c' : Fin n' → F)
    (t : Fin n → T) (t' : Fin n' → T) (v : T → O) :
    ∑ i, g (Fin.append c (-c') i) * v (Fin.append t t' i) =
      ∑ i, g (c i) * v (t i) - ∑ i, g (c' i) * v (t' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end ExpansionSingleValued


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep ExpansionSingleValued in
theorem expandsG_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : U.SecGF F k) (s s₂ : Fam D.toPre F k), U.ExpandsG F k σ s → U.ExpandsG F k σ s₂ → s = s₂ := by
  intro R _ _ I hR D A G _ _ U k F _ _ σ s s₂ ⟨n, c, τ, f, hE, hG, hB⟩ ⟨n', c', τ', f', hE', hG', hB'⟩
  let : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords R F (Fin.append c (-c'))
  have := U.smooth
  have hz : ∀ l α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (a i l)) * (Fin.append f f' i α).f j = 0 := fun l => by
    refine (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k _ (fun i => a i l) (Fin.append τ τ')
      (Fin.append f f') (fun i => ?_)).1 fun j => ?_
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hE i
      · simpa only [Fin.append_right] using hE' i
    refine fn_ext fun x hx => (gs_scal_comb G.hom (𝟙 _) x hx _ _).trans (Eq.trans ?_ (gs_zero _ _ _ hx).symm)
    rw [Category.id_comp]
    refine split_relation G.hom x hx b hb a (fun i => (Fin.append τ τ' i).f j) (fun Z q r hr z hz => ?_) l
    let ρ₀ : Z ⟶ pullback G.hom (jK R) := pullback.lift r (q ≫ jFK (R := R) F) (by rw [hr, Category.assoc, hj])
    let ρ : Z ⟶ (UnifPre.GF (G := G) F).left := pullback.lift q ρ₀ (pullback.lift_snd _ _ _).symm
    have e₁ : ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = q := pullback.lift_fst _ _ _
    have e₂ : ρ ≫ UnifPre.gFK (G := G) F = r :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom (jK R)) (pullback.lift_snd _ _ _)).trans
        (pullback.lift_fst _ _ _))
    obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Fin 1 => r ≫ 𝟙 _) j
      (fun u v _ => congrArg j (Subsingleton.elim u v)) (fun u => Set.mem_iInter.1 hz u)
    have h₁ := ExpGTrans.secLin_val hG ρ z hJ
    have h₂ := ExpGTrans.secLin_val hG' ρ z hJ
    simp only [gs_scal, e₂, sval_of _ r z J j eJ] at h₁ h₂
    simp only [← ha]
    refine (sum_append (germOf q z) c c' τ τ' (fun t => gs r z _ (t.f j))).trans (sub_eq_zero.2 ?_)
    rw [← e₁]
    exact h₁.symm.trans h₂
  refine fam_ext fun α => sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
  rw [ExpGTrans.secLin_val (hB α) _ y hJ, ExpGTrans.secLin_val (hB' α) _ y hJ]
  simp only [gs_scal]
  set q := 𝟙 _ ≫ (fst (TF (R := R) F) D.toPre.P.A).left
  set r := 𝟙 _ ≫ (DegPre.prB D.toPre F).left
  have e : r ≫ D.toPre.P.A.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [Category.assoc, Category.assoc, Over.w, ← hj]
    exact congrArg _ (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine sub_eq_zero.1 ((sum_append (germOf q y) c c' f f' (fun t => sval (t α) r y J)).symm.trans ?_)

  simp only [ha, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hm := hJ.mem (D.toPre.famφB α) r
  have h := (gs_scal_comb D.toPre.P.A.hom r y hm _ _).symm.trans
    ((congrArg _ (hz l α _)).trans (gs_zero _ _ _ hm))
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q y (b l))).symm.trans
    ((congrArg _ h).trans (mul_zero _)))
  rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q y _), _root_.mul_assoc]
  rfl

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.exists_gen_of_torusEnd_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  first | exact @GlobalTheory.gtCoord_end_ratio_descends | exact GlobalTheory.gtCoord_end_ratio_descends | (intros; apply GlobalTheory.gtCoord_end_ratio_descends <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_translate_torsion_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → gp.b ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k))) (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)])) (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α) (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k))), ν.IsGen ∧ uL.IsGen ∧ (∀ α, (uM α).IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uM α) (eSec D.toPre.P.A)) (LB.mulGen D.toPre.P.L _ _ _ _ (gp.s α) ν)) ∧ ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α), GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL → (∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α)) → ∀ e, U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  first | exact @GlobalTheory.expandsAt_translate_torsion | exact GlobalTheory.expandsAt_translate_torsion | (intros; apply GlobalTheory.expandsAt_translate_torsion <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem exists_fraction_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    ∃ g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)),
      g ≫ jK R = jK R' ≫ specOf φ ∧ jFK (R := R') F ≫ g = jFK (R := R) F := by
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (injective_iff_map_eq_zero _).2 fun r hr => by
      have e := hF r
      rw [show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero] at e
      exact (IsFractionRing.injective R (FractionRing R))
        (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)
  obtain ⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R',
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · exact (Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))
  · exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)

theorem grp_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl

end GlobalTheory.ThetaBaseChange

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange in

theorem qkToAk_baseChange : GlobalFnsSt → SecBaseChangeSt → QkBaseChangeSt := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)
  obtain ⟨ν, hν, Hν⟩ := H θ hθ
  obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν
  refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
  have bij := (expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1
  have bij' := (expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧
      U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij a).exists
    refine ⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩
    obtain ⟨σ', h₁', -⟩ := E
    exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
      Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
      (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
  obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
  obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
  exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

noncomputable def transl (x : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ x)

theorem comp_transl (x : 𝟙_ (Over S) ⟶ A) {T : Over S} (y : T ⟶ A) : y ≫ transl x = y * (toUnit T ≫ x) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem toUnit_mul_self {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) (T : Over S) :
    (toUnit T ≫ x) * (toUnit T ≫ x) = 1 := by
  rw [← MonObj.comp_mul, hx, MonObj.comp_one]

theorem transl_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) : transl x ≫ transl x = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]

theorem inv_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) :
    (GrpObj.inv : A ⟶ A) ≫ transl x = transl x ≫ (GrpObj.inv : A ⟶ A) := by
  rw [comp_transl, ← Hom.inv_def, transl, mul_inv, inv_eq_of_mul_eq_one_right (toUnit_mul_self hx A), Hom.inv_def,
    Category.id_comp]

theorem exists_restrict {X Y : Scheme.{0}} (p : X ⟶ Y) (h : X ⟶ X) (e : h ≫ p = p) (V : Y.Opens) :
    ∃ n : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme, n ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ h :=
  ⟨IsOpenImmersion.lift _ ((p ⁻¹ᵁ V).ι ≫ h) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y.1 ∈ V) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩

theorem sym_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (h : Sym A L) :
    Sym A (L.pull (transl x).left) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := exists_restrict A.hom (transl x).left (Over.w _) U
  refine ⟨U, hU, _, LBxP.isGen_pullAlong L (transl x).left n _ _ _ (fun k => ?_) t ht⟩
  fin_cases k
  · show (_ ≫ _) ≫ _ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    exact congrArg (fun q => _ ≫ q.left) (inv_transl hx)
  · exact hn.symm

theorem kTriv_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (hL : L.IsLB) (h : KTriv A L) :
    KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x))) V
  have k₂ : T ◁ transl x ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_transl hx, Category.comp_id]
  have k₃ : T ◁ transl x ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end GlobalTheory.PolTranslate
end
