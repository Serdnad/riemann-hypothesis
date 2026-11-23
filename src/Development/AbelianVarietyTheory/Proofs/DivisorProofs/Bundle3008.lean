module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiFormAdj

theorem real_eq_of_exp {p : ℤ} {r : ℝ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / n)) : (p : ℝ) = r := by
  have h1 := h 1 one_pos
  simp only [Nat.cast_one, div_one] at h1
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hr : (r : ℂ) = ((p + m : ℤ) : ℂ) := by
    have := Complex.two_pi_I_ne_zero
    push_cast
    apply mul_left_cancel₀ this
    linear_combination hm
  have hr' : r = ((p + m : ℤ) : ℝ) := by exact_mod_cast hr
  have := GlobalTheory.HermAdjoint.int_eq_of_exp (p := p) (q := p + m) (fun n hn => by rw [h n hn, hr])
  rw [hr', ← this]

theorem lbIso_pull_iff_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF he hQ hker hW f f' u u' hf hf' hu hu'
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  obtain ⟨v, Hm, χ, hve, hAH⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_exponential A g hA hg e he M hM
  have hN : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hND := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM A (𝟙 A) (𝟙 A)
  have hmem : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => (v.ker z).symm.trans (by rw [hve]; exact hker z)
  have hEF : ∀ a b, (EF a b : ℝ) = 2 * (hermForm Hm (Q a) (Q b)).im := by
    intro a b
    apply real_eq_of_exp
    intro k hk
    have hc := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)
    have hc' := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm (Q a) (Q b)).im : ℝ)) : ℂ) / k)
    have w1 := hW k a b (Units.mk0 _ hc) hk rfl
    have w2 := GlobalTheory.T.commutator_pairing_diagonal_mumford_bundle A g hA hg M v Hm χ hM hAH _ hN hND hamp k (Q a) (Q b) (Units.mk0 _ hc') hk
      ((hmem _).2 ⟨a, rfl⟩) ((hmem _).2 ⟨b, rfl⟩) rfl
    rw [hve, hve] at w2
    exact congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ hN (𝟙 (Sp ℂ)) k _ _ _ _ w1 w2)
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f he he hf
  obtain ⟨F', hF', -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f' he he hf'
  have hlift : ∀ (G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (w : La →+ La), (∀ z, e (G z) = e z ≫ φ) →
      (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (w x)) = e ((k : ℂ)⁻¹ • Q x) ≫ φ) → ∀ x, G (Q x) = Q (w x) := by
    intro G φ w hG hw x
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_inv_nat_smul_mem_discrete_submodule g v.Λ v.discrete (G (Q x) - Q (w x)) fun k hk => ?_)
    refine (hmem _).2 ((hker _).1 ?_)
    have e1 : e ((k : ℂ)⁻¹ • G (Q x)) = e ((k : ℂ)⁻¹ • Q (w x)) := by
      rw [← map_smul, hG, hw k x hk]
    have e2 := he.1 ((k : ℂ)⁻¹ • (G (Q x) - Q (w x))) ((k : ℂ)⁻¹ • Q (w x))
    rw [← smul_add, sub_add_cancel, e1] at e2
    exact mul_eq_right.1 e2.symm
  have hFQ := hlift F f u hF hu
  have hFQ' := hlift F' f' u' hF' hu'
  have hvF : ∀ z, v.ex (F z) = v.ex z ≫ f := fun z => by rw [hve, hve]; exact hF z
  have hvF' : ∀ z, v.ex (F' z) = v.ex z ≫ f' := fun z => by rw [hve, hve]; exact hF' z
  have hisoL := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A ≫ f) (snd A A)
  have hisoR := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A) (snd A A ≫ f')
  have hcl : ∀ (a b : A ⊗ A ⟶ A), (cubeLB A ![a, b] M).IsLB := fun a b => LB.isLB_linComb hM _ _
  have key : LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔
      LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
    constructor
    · intro h
      exact LBIso.trans (hcl _ _) (pull_isLB hP _) (hcl _ _) hisoL.symm
        (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (hcl _ _) h hisoR)
    · intro h
      exact LBIso.trans (pull_isLB hP _) (hcl _ _) (pull_isLB hP _) hisoL
        (LBIso.trans (hcl _ _) (hcl _ _) (pull_isLB hP _) h hisoR.symm)
  rw [key]
  constructor
  · intro h x y
    have := GlobalTheory.T.adjoint_appellHumbertForm_of_mumfordBundle_lbIso A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF' h (Q x) (Q y)
    have hh : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by
      rw [hEF, hEF, ← hFQ, ← hFQ', this]
    exact_mod_cast hh
  · intro h
    apply GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF'
    refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ v.full fun a ha b hb => ?_
    obtain ⟨x, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, rfl⟩ := (hmem b).1 hb
    have h1 := hEF (u x) y
    have h2 := hEF x (u' y)
    have h3 : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by rw [h x y]
    rw [hFQ, hFQ']
    linarith

end GlobalTheory.RosatiFormAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem Near.closed_product_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  intro R _ _ _ M G' _ E N fU l hl1 hl2 hsurj Ω _ κ s s' a b c c' x y x' y' hs hs' ha hb hc ha' hb' hc'
  obtain ⟨Ω₁, _, io₁, ca, cb, hca, hcb, hcc⟩ := GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s a b c x y hs ha hb hc
  obtain ⟨Ω₂, _, io₂, ca', cb', hca', hcb', hcc'⟩ :=
    GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s' a b c' x' y' hs' ha' hb' hc'
  obtain ⟨Ω₃, _, j₁, j₂, hj⟩ := GlobalTheory.T.exists_common_field_extension' Ω Ω₁ Ω₂ io₁ io₂
  have : Mono E.j := by haveI := E.imm; infer_instance

  let g₁ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₁.comp κ)) :=
    Over.homMk (spMap j₁) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom])
  let g₂ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₂.comp κ)) :=
    Over.homMk (spMap j₂) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom, hj])
  have hg₁ : g₁.left = spMap j₁ := rfl
  have hg₂ : g₂.left = spMap j₂ := rfl
  have e₁ : spMap j₁ ≫ spMap io₁ = spMap (j₁.comp io₁) := specMap_contravariant_comp_ringHom _ _
  have e₂ : spMap j₂ ≫ spMap io₂ = spMap (j₁.comp io₁) := by rw [specMap_contravariant_comp_ringHom, hj]
  have hA : g₁ ≫ ca = g₂ ≫ ca' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hca, hca']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hB : g₁ ≫ cb = g₂ ≫ cb' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcb, hcb']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hC : g₁ ≫ (ca * cb) = g₂ ≫ (ca' * cb') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hA, hB]
  have hfU : spMap (j₁.comp io₁) ≫ c ≫ fU = spMap (j₁.comp io₁) ≫ c' ≫ fU := by
    have := congrArg (fun g => g.left ≫ E.j) hC
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcc, hcc'] at this
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂] at this
    exact this

  have hlies : ∀ (t : Sp Ω ⟶ M.S) (d : Sp Ω ⟶ N.U.left) (z : Sp Ω ⟶ G'.left), t ≫ M.π = spMap (κ.comp (residue R)) →
      N.Pt t d z → d ≫ N.U.hom = spMap (κ.comp (residue R)) := by
    rintro t d z ht ⟨x₀, h₁, h₂, -⟩
    rw [← h₁, Category.assoc, pullback.condition, ← Category.assoc, h₂, ht]
  have hco : ∀ d : Sp Ω ⟶ N.U.left, d ≫ N.U.hom = spMap (κ.comp (residue R)) →
      (spMap (j₁.comp io₁) ≫ d) ≫ N.U.hom = spMap (((j₁.comp io₁).comp κ).comp (residue R)) := by
    intro d hd
    rw [Category.assoc, hd, specMap_contravariant_comp_ringHom]
  have key := GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map R M G' E N fU l hl1 hl2 hsurj Ω₃ ((j₁.comp io₁).comp κ) (spMap (j₁.comp io₁) ≫ c)
    (spMap (j₁.comp io₁) ≫ c') (hco c (hlies s c _ hs hc)) (hco c' (hlies s' c' _ hs' hc'))
    (by simpa only [Category.assoc] using hfU)
  exact GlobalTheory.T.spMap_field_ext_cancel Ω Ω₃ (j₁.comp io₁) N.U.left c c' key

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GalDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem restrict_act {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} {Y Y' Z : Scheme.{0}}
    {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β)
    (hy' : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) (f : Z ⟶ Y) :
    ∃ act' : Gal ρ → (pullback β f ⟶ pullback β f), (∀ σ, act' σ ≫ pullback.snd β f = pullback.snd β f) ∧
      (∀ σ, act' σ ≫ (pullback.fst β f ≫ y') = (pullback.fst β f ≫ y') ≫ spMap (Gal.hom σ)) ∧
      ∀ σ, act' σ ≫ pullback.fst β f = pullback.fst β f ≫ act σ := by
  refine ⟨fun σ => pullback.lift (pullback.fst β f ≫ act σ) (pullback.snd β f)
    (by rw [Category.assoc, hβ, pullback.condition]), fun σ => pullback.lift_snd _ _ _, fun σ => ?_,
    fun σ => pullback.lift_fst _ _ _⟩
  rw [pullback.lift_fst_assoc, Category.assoc, hy', Category.assoc]

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), β ≫ g₁ = β ≫ g₂ → g₁ = g₂ := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g₁ g₂ he
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := β.surjective x
    have := congrArg (fun k : Y' ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (β.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _
    (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' _).1
  rw [← cancel_mono (β.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) [IsAffine W] (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃ h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W _ h hh
  obtain ⟨hinj, hdesc⟩ := GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ Set.range (β.app ⊤).hom := by
    intro x
    refine hdesc (h.appTop x) fun σ hle => ?_
    have e : h.appTop ≫ (act σ).appTop = h.appTop := by rw [← Scheme.Hom.comp_appTop, hh]
    have e' : (act σ).appLE (β ⁻¹ᵁ ⊤) (β ⁻¹ᵁ ⊤) hle = (act σ).appTop := by
      rw [Scheme.Hom.appLE]
      exact (congrArg ((act σ).app ⊤ ≫ ·) (Y'.presheaf.map_id _)).trans (Category.comp_id _)
    rw [e']
    exact congrArg (fun k => k.hom x) e
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ β.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Y'.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc β, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃! h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W h hh
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin.2.2
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hβF : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hF
  have : Finite (Gal ρ) := hgal.1
  have hsp : ∀ σ τ : Gal ρ, spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := fun σ τ => by
    rw [← Spec.map_comp]; rfl
  have hsp1 : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by rw [← Spec.map_id]; rfl
  have e1 : act 1 = 𝟙 Y' := hpb.hom_ext (by rw [hβ, Category.id_comp])
    (by rw [hy', Category.id_comp, hsp1, Category.comp_id])
  have e2 : ∀ σ τ, act (σ * τ) = act σ ≫ act τ := fun σ τ => hpb.hom_ext
    (by rw [hβ, Category.assoc, hβ, hβ])
    (by rw [hy', Category.assoc, hy', ← Category.assoc, hy', Category.assoc, hsp])
  have ei : ∀ σ, act σ ≫ act σ⁻¹ = 𝟙 Y' := fun σ => by rw [← e2, mul_inv_cancel, e1]
  have ei' : ∀ σ, act σ⁻¹ ≫ act σ = 𝟙 Y' := fun σ => by rw [← e2, inv_mul_cancel, e1]
  let ρ' : Gal ρ →* Aut Y' :=
    { toFun := fun σ => ⟨act σ⁻¹, act σ, ei' σ, ei σ⟩
      map_one' := by
        apply Aut.ext
        apply Iso.ext
        change act 1⁻¹ = 𝟙 Y'
        rw [inv_one, e1]
      map_mul' := by
        intro σ τ
        apply Aut.ext
        apply Iso.ext
        change act (σ * τ)⁻¹ = act τ⁻¹ ≫ act σ⁻¹
        rw [mul_inv_rev, e2] }
  have hρ' : ∀ g, (ρ' g).asIso.hom ≫ β = β := fun g => hβ g⁻¹
  have hinv : ∀ V : Y.Opens, IsAffineOpen V → ∀ s : Γ(Y', β ⁻¹ᵁ V),
      GlobalTheory.IsInvariantSection ρ' _ s → s ∈ Set.range (β.app V) := by
    intro V _ s hs
    refine (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' V).2 s fun σ hle => ?_
    obtain ⟨h1, h2⟩ := hs σ⁻¹
    have key : ∀ (k : Y' ⟶ Y') (_ : k = act σ) (e : β ⁻¹ᵁ V ≤ k ⁻¹ᵁ (β ⁻¹ᵁ V)),
        (k.appLE _ _ e).hom s = s → ((act σ).appLE _ _ hle).hom s = s := by
      rintro k rfl e h; exact h
    exact key _ (show act σ⁻¹⁻¹ = act σ by rw [inv_inv]) h1 h2
  have hfib : Function.FactorsThrough h.base.hom β.base.hom := by
    intro a b hab
    obtain ⟨g, rfl⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant ρ' β hρ' hinv a b).1 hab
    show h a = h ((act g⁻¹) a)
    rw [← Scheme.Hom.comp_apply, hh]
  have hq : Topology.IsQuotientMap β.base.hom :=
    IsClosedMap.isQuotientMap β.isClosedMap β.base.hom.continuous β.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (β z) = h z := fun z => congrArg (fun k : C(Y', W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd β (V i).ι ≫ u = pullback.fst β (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst β (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd β (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    obtain ⟨act', ha1, ha2, ha3⟩ := restrict_act act hβ hy' (V i).ι
    have hinv' : ∀ σ, act' σ ≫ hi = hi := fun σ => by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      rw [reassoc_of% (ha3 σ), hh]
    obtain ⟨u, hu⟩ := exAff R R' ρ hfin hgal (V i).toScheme (pullback β (V i).ι) ((V i).ι ≫ y)
      (pullback.fst β (V i).ι ≫ y') (pullback.snd β (V i).ι) inferInstance (restrict_isPullback hpb _)
      act' ha1 ha2 i.1.toScheme hi hinv'
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    obtain ⟨act', ha1, ha2, -⟩ := restrict_act act hβ hy' f
    apply uniq R R' ρ hfin hgal _ (pullback β f) (f ≫ y) (pullback.fst β f ≫ y') (pullback.snd β f)
      inferInstance (restrict_isPullback hpb f) act' ha1 ha2 W
    let mi : pullback β f ⟶ pullback β (V i).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback β f ⟶ pullback β (V j).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd β (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd β f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd β (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : β ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ β) _ _ fun i => ?_
    change pullback.fst β (V i).ι ≫ _ = pullback.fst β (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd β (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd β (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g _ (hg.trans hglue.symm)

end GlobalTheory.GalDescent
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalFibre

theorem exists_act_apply_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ →
    ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) →
    ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) →
    ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  intro R R' _ _ ρ _ hG Y X p p' β hfl hpb act hact hactβ z₀ z hz
  have : Flat p := hfl
  let π : R →+* ρ.range := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hfac : spMap ρ = spMap (algebraMap ρ.range R') ≫ spMap π := by
    rw [← Spec.map_comp]; rfl
  have hsq : IsPullback (pullback.fst p (spMap π)) (pullback.snd p (spMap π)) p (spMap π) :=
    IsPullback.of_hasPullback _ _
  let p₀ : X ⟶ pullback p (spMap π) :=
    hsq.lift β (p' ≫ spMap (algebraMap ρ.range R')) (by rw [hpb.w, hfac, Category.assoc])
  have hp₀ : p₀ ≫ pullback.fst p (spMap π) = β := hsq.lift_fst _ _ _
  have hp₀' : p₀ ≫ pullback.snd p (spMap π) = p' ≫ spMap (algebraMap ρ.range R') := hsq.lift_snd _ _ _
  have outer : IsPullback (p₀ ≫ pullback.fst p (spMap π)) p' p (spMap (algebraMap ρ.range R') ≫ spMap π) := by
    rw [hp₀, ← hfac]; exact hpb
  have hpb₀ : IsPullback p₀ p' (Over.mk (pullback.snd p (spMap π))).hom (spMap (algebraMap ρ.range R')) :=
    IsPullback.of_right outer hp₀' hsq
  have hinj : Function.Injective (algebraMap ρ.range R') := Subtype.val_injective
  let toG : Gal (algebraMap ρ.range R') → Gal ρ := fun σ => ⟨σ.1, fun r => σ.2 (π r)⟩
  have hG₀ : IsGal (algebraMap ρ.range R') := by
    refine ⟨?_, fun x hx => ?_⟩
    · have : Finite (Gal ρ) := hG.1
      exact Finite.of_injective toG (fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun s : Gal ρ => s.1) h))
    · have hx' : ∀ σ ∈ Gal ρ, σ x = x := fun σ hσ => by
        refine hx σ ?_
        rintro ⟨_, r, rfl⟩
        exact hσ r
      exact ⟨⟨x, hG.2 x hx'⟩, rfl⟩
  have hflat : Flat (Over.mk (pullback.snd p (spMap π))).hom := by
    change Flat (pullback.snd p (spMap π)); infer_instance
  have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  have hz₀ : p₀ z₀ = p₀ z := by
    apply (pullback.fst p (spMap π)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp₀, hz]
  obtain ⟨σ', h, h₁, h₂, h₃⟩ := gal_transitive_on_fibres ρ.range R' hinj hG₀ (Over.mk (pullback.snd p (spMap π)))
    hflat X p₀ p' hpb₀ z₀ z hz₀
  refine ⟨toG σ', ?_⟩
  have he : act (toG σ') = h := by
    refine hpb.hom_ext ?_ ?_
    · rw [hactβ, ← hp₀, ← Category.assoc, h₁]
    · rw [hact, h₂]; rfl
  rw [he, h₃]

end GlobalTheory.Mum.GalFibre
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.lift_sections_next_thickening_standardCharts : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  first | exact @GlobalTheory.FormalAlg.lift_cech | exact GlobalTheory.FormalAlg.lift_cech | (intros; apply GlobalTheory.FormalAlg.lift_cech <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PeriodSpan

theorem main : PSpan := by
  intro A _ g hA _ L u P hP
  exact GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods A g L u hA P fun c =>
    GlobalTheory.T.crystalline_period_eq_cechDeRham_period A g L u c.1
      { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
      _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodSpan
end
