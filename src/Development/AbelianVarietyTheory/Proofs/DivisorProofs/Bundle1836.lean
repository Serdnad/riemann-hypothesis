module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle722
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.LocGlobRing

noncomputable def pbIso (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap A O))) ≅ Spec (CommRingCat.of (O ⊗[A] X)) :=
  pullback.congrHom hg rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso A O X

theorem pbIso_inv_fst (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : X →ₐ[A] O ⊗[A] X).toRingHom) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_snd]

theorem pbIso_inv_snd (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : O →+* O ⊗[A] X)) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_fst]

end GlobalTheory.LocGlobRing

namespace GlobalTheory.LocGlobRing

theorem square (A B C O : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing O] [Algebra A B] [Algebra A C] [Algebra A O]
    (φ : B →ₐ[A] C)
    (hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (h₁ h₂) :
    (pbIso A C O _ hC).inv ≫ pullback.map (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (𝟙 _) h₁ h₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) ≫ (pbIso A B O _ rfl).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pbIso_inv_fst, Category.assoc, pbIso_inv_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pbIso_inv_snd, Category.assoc, pbIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    ext x
    simp

end GlobalTheory.LocGlobRing

theorem GlobalTheory.LocGlobRing.main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  intro R _ F hF A B C _ _ _ _ _ φ hyp
  have hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks R F hF (Spec (CommRingCat.of C)) (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hInd, rfl⟩ := GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine A O s hs
  have h := @hyp O _ inst hSH hInd
  have eb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  rw [← Iso.hom_inv_id_assoc (GlobalTheory.LocGlobRing.pbIso A C O _ hC) (pullback.map _ _ _ _ _ _ _ _ _),
    GlobalTheory.LocGlobRing.square A B C O φ hC, Functor.map_comp, Functor.map_comp]
  exact (eb.2.1 _ _ _ _ _).1 (eb.1 _ _ _ inferInstance) ((eb.2.1 _ _ _ _ _).1 h (eb.1 _ _ _ inferInstance))
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.strongApproximation_quaternion_normOne_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_nrm_one | exact GlobalTheory.QSA.strongApprox_nrm_one | (intros; apply GlobalTheory.QSA.strongApprox_nrm_one <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_periodic_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ i, IsReg u.ex (W i) (h i) := by
  intro A _ g L u hA K W h hW hd hp hr
  obtain ⟨hopen, -, hpre, hval, hinf, -, hsup, -, -, -, -, htop⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have glue := GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA
  have alg := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u
  obtain ⟨n, V, r, hV⟩ := GlobalTheory.T.exists_complexAbelianVariety_sectionRatio_affine_cover A g L u hA
  have tor := fun c : Fin n => GlobalTheory.T.exists_regular_section_of_regular_differences A g L u hA K W h hW hr ⟨V c, hV.1 c⟩
  choose k hk using tor
  have hk' : ∀ c i, IsReg u.ex (V c ⊓ W i) (k c - h i) := hk
  have covW : ∀ z, ∃ i, z ∈ pre u.ex (W i) := fun z => (hsup K W z).1 (hW ▸ htop z)
  have covV : ∀ z, ∃ c, z ∈ pre u.ex (V c) := fun z => (hsup (Fin n) V z).1 (hV.2.1 ▸ htop z)
  have hreg : ∀ c, IsReg u.ex (V c) (k c) := by
    refine GlobalTheory.T.regular_of_periodic_regular_differences_ratio_cover A g L u hA n V r hV k (fun c z hz => ?_) (fun c l z hz => ?_) (fun c c' => ?_)
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      have h1 : DifferentiableAt ℂ (k c - h i) z :=
        ((alg _).2.2.2.2.1 _ (hk' c i) z hz').differentiableAt ((hopen _).mem_nhds hz')
      have h2 : DifferentiableAt ℂ (h i) z := (hd i z hi).differentiableAt ((hopen _).mem_nhds hi)
      have h3 := h1.add h2
      rw [sub_add_cancel] at h3
      exact h3.differentiableWithinAt
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      obtain ⟨b, hb⟩ := hk' c i
      have e1 := hb z hz'
      have e2 := hb _ ((hpre _ l z).2 hz')
      rw [hval, ← e1, Pi.sub_apply, Pi.sub_apply, hp i l z hi] at e2
      exact sub_left_injective e2
    · refine glue _ _ fun z hz => ?_
      obtain ⟨i, hi⟩ := covW z
      refine ⟨V c ⊓ V c' ⊓ W i, inf_le_left, by rw [hinf]; exact ⟨hz, hi⟩, ?_⟩
      have r1 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_left) _ (hk' c i)
      have r2 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_right) _ (hk' c' i)
      have r3 := ((alg _).2.1 _ _ r1 r2).2.1
      rwa [sub_sub_sub_cancel_right] at r3
  intro i
  refine glue _ _ fun z hz => ?_
  obtain ⟨c, hc⟩ := covV z
  refine ⟨V c ⊓ W i, inf_le_right, by rw [hinf]; exact ⟨hc, hz⟩, ?_⟩
  have r1 := (alg _).2.2.2.1 (V c ⊓ W i) inf_le_left _ (hreg c)
  have r3 := ((alg _).2.1 _ _ r1 (hk' c i)).2.1
  rwa [sub_sub_cancel] at r3

end GlobalTheory.CechPer
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Exist

theorem exists_isKW : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψn hψ1 χ hχ hη _ _ μ _
  obtain ⟨hFD, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hFD
  obtain ⟨hMT, hGood⟩ := hM α ν
  haveI := hMT
  haveI := hGood.grp
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have h := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψn hψ1 β hβs hβn
    simpa only [hβ] using h
  have hfm : ∀ φ ∈ SB (Matrix α ν E), fou c ψ Q μ φ ∈ SB (Matrix α ν E) := fun φ hφ =>
    GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hGood μ _ hpair φ hφ
  have hpm := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨hp1, hpmul⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨κ, hκ, hrel⟩ := GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ
  obtain ⟨C, hC, hff⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hGood μ _ hpair

  let parL : sieg c ν → Module.End ℂ (SB (Matrix α ν E)) := fun p =>
    { toFun := fun φ => ⟨parFun c ψ χ Q (mat c p) φ, hpm p p.2 φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring) }
  let ρ₀ : sieg c ν →* Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := parL
      map_one' := LinearMap.ext fun φ => Subtype.ext (hp1 φ)
      map_mul' := fun p q => LinearMap.ext fun φ => Subtype.ext (hpmul p p.2 q q.2 φ) }

  have hint : ∀ φ : Matrix α ν E → ℂ, φ ∈ SB (Matrix α ν E) → ∀ x,
      Integrable (fun y => ψ (pr c Q x y) * φ y) μ := by
    intro φ hφ x
    have hlc : IsLocallyConstant (fun y => ψ (pr c Q x y) * φ y) :=
      (hpair.lc.comp_continuous (continuous_const.prodMk continuous_id)).mul hφ.1
    exact hlc.continuous.integrable_of_hasCompactSupport hφ.2.mul_left
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ) x, fou c ψ Q μ (k • f) x = k * fou c ψ Q μ f x := by
    intro k f x
    simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  let Fo : Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := fun φ => ⟨fou c ψ Q μ φ, hfm φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [fou, four, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2 x) (hint _ φ'.2 x))
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fou_smul z _ x) }
  have hne : (κ ^ 2 * (C : ℂ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ) (by exact_mod_cast hC.ne')
  have key : ∀ φ : SB (Matrix α ν E),
      (((κ • Fo) ((κ • Fo) φ) : SB (Matrix α ν E)) : Matrix α ν E → ℂ) = fun x => (κ ^ 2 * (C : ℂ)) * (φ : Matrix α ν E → ℂ) (-x) := by
    intro φ
    funext x
    show κ * fou c ψ Q μ (κ • fou c ψ Q μ φ) x = _
    rw [fou_smul]
    have h := hff φ φ.2 x
    change fou c ψ Q μ (fou c ψ Q μ φ) x = _ at h
    rw [h]
    ring
  have hW : IsUnit (κ • Fo) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have h2 := congrArg (fun φ => (((κ • Fo) φ : SB (Matrix α ν E)) : Matrix α ν E → ℂ)) hab
      simp only [key] at h2
      apply Subtype.ext
      funext x
      have h3 := congrFun h2 (-x)
      simp only [neg_neg] at h3
      exact mul_left_cancel₀ hne h3
    · intro φ
      have hr : (fun x => (φ : Matrix α ν E → ℂ) (-x)) ∈ SB (Matrix α ν E) :=
        ⟨φ.2.1.comp_continuous continuous_neg, φ.2.2.comp_homeomorph (Homeomorph.neg _)⟩
      refine ⟨(κ ^ 2 * (C : ℂ))⁻¹ • (κ • Fo) ⟨_, hr⟩, Subtype.ext (funext fun x => ?_)⟩
      rw [map_smul, Submodule.coe_smul, Pi.smul_apply, key]
      simp only [neg_neg, smul_eq_mul]
      exact inv_mul_cancel_left₀ hne _
  obtain ⟨Φ, hΦp, hΦw⟩ := GlobalTheory.T.exists_hom_of_bigCell_generic_relations (UG c (stdJ ν E)) (Module.End ℂ (SB (Matrix α ν E)))ˣ (sieg c ν)
    (weyl c ν) ρ₀.toHomUnits hW.unit
    (by
      intro p q hpq
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext x
      have h := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ p p.2 q q.2 hpq φ
      show κ * fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) x =
        parFun c ψ χ Q (mat c q) (κ • fou c ψ Q μ φ) x
      rw [h]
      simp only [parFun, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      rintro p ⟨p₁, p₂, h⟩
      obtain ⟨q₁, hq₁, q₂, hq₂, he, hop⟩ := hrel p p.2 ⟨p₁, p₁.2, p₂, p₂.2, h⟩
      refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, he, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact hop φ φ.2)
    (by
      intro s
      obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν s
      refine ⟨u, fun g hg => ?_⟩
      obtain ⟨p, hp, q, hq, h⟩ := hu g hg
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩)
  refine ⟨κ, (Units.coeHom _).comp Φ, ⟨fun p hp φ => ?_, fun φ => ?_⟩⟩
  · have h := hΦp ⟨p, hp⟩
    change ((Φ ((⟨p, hp⟩ : sieg c ν) : UG c (stdJ ν E)) : Module.End ℂ (SB (Matrix α ν E))) φ :
      Matrix α ν E → ℂ) = _
    rw [h]
    rfl
  · change ((Φ (weyl c ν) : Module.End ℂ (SB (Matrix α ν E))) φ : Matrix α ν E → ℂ) = _
    rw [hΦw, IsUnit.unit_spec]
    rfl

end GlobalTheory.KSp.Exist

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  first | exact @GlobalTheory.PELU.unifAt_cmp | exact GlobalTheory.PELU.unifAt_cmp | (intros; apply GlobalTheory.PELU.unifAt_cmp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  first | exact @GlobalTheory.ExpLin.exists_ringHom_matrix_lift | exact GlobalTheory.ExpLin.exists_ringHom_matrix_lift | (intros; apply GlobalTheory.ExpLin.exists_ringHom_matrix_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

private lemma add_add_eq_add_imp {M : Type} [AddCommGroup M] (a b c d : M) (h : (a + b) + (c + d) = a + d) :
    c + b = 0 := by
  calc c + b = (a + b) + (c + d) - (a + d) := by abel
    _ = 0 := by rw [h, sub_self]

theorem wsum_eq_zero_of_mul : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (n : ℕ) (u v : Fin n → GlobForm A.hom), wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) = wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) + wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) → wsum (OAff A.hom) u v = 0 := by
  intro R _ A _ g hA hs n u v hw
  have hP : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  obtain ⟨hF, hC, hA2, hs2⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨-, hax, -⟩ := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  let U : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (snd A A) (u k))
  let V : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (snd A A) (v k)) (fun k ↦ pF (fst A A) (v k))
  have hUV : wsum (OAff (A ⊗ A).hom) U V = 0 := by
    funext T
    have h1 := congrFun hw T
    simp only [wsum, hP, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply,
      Finset.sum_add_distrib] at h1
    simp only [wsum, Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right]
    exact add_add_eq_add_imp _ _ _ _ h1
  have key := (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R _ (OAff (A ⊗ A).hom) hF2 hC2 (n + n) U V).mp hUV
  refine (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R _ (OAff A.hom) hF hC n u v).mpr ?_
  intro l l'
  have h2 := key (l ∘ₗ pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (l' ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  simp only [Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right, LinearMap.comp_apply,
    (hax _).1, (hax _).2.1, (hax _).2.2.2.1, (hax _).2.2.2.2.1, map_zero, mul_zero, zero_mul, sub_zero,
    zero_sub] at h2
  rw [← h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbCoh.primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A :=
  fun R _ A _ g hA hg ↦ GlobalTheory.AbCoh.PrimForm.prim_of_axes A (GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes R A g hA hg)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.CohBaseChange

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s :=
  of_parts (@GlobalTheory.AbCoh.exists_finite_projective_model) (@GlobalTheory.AbCoh.projective_coker_of_liftsAt) (@GlobalTheory.AbCoh.cohom_split_baseChange)

end GlobalTheory.AbCoh.CohBaseChange
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem wedgeO_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  intro K L _ _ _ A _ B _ φ h hA hB
  have hp : IsProper A.hom := hA.proper
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ :=
    GlobalTheory.T.structure_cohomology_flat_base_change K L A.left B.left A.hom B.hom φ h.1 inferInstance inferInstance
  refine GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field K L _ _ _ _ (cup (OAff A.hom)) (cup (OAff B.hom)) e₁ e₂ (fun a b ↦ ?_) hB
  rw [he₁, he₁, he₂]
  exact (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.1 K L A.left B.left A.hom B.hom _ φ h.1.w).1 a b

end GlobalTheory.AbCoh
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.kernelDegree_le_dieudonneColength : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  first | exact @GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | exact GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.le_length_coker_of_hasLogDeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  first | exact @GlobalTheory.DualLocus.exists_closed_same | exact GlobalTheory.DualLocus.exists_closed_same | (intros; apply GlobalTheory.DualLocus.exists_closed_same <;> assumption)
end
