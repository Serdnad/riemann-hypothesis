module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finiteType_additiveLineBundleFamily_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  first | exact @GlobalTheory.DualApprox.exists_fam_finiteType | exact GlobalTheory.DualApprox.exists_fam_finiteType | (intros; apply GlobalTheory.DualApprox.exists_fam_finiteType <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFinite_twisted_kernel_cubeLambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | exact GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | (intros; apply GlobalTheory.TwistKerFinite.isFinite_twisted_kernel <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  first | exact @GlobalTheory.DualCon.same_of_fpqc | exact GlobalTheory.DualCon.same_of_fpqc | (intros; apply GlobalTheory.DualCon.same_of_fpqc <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f → GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  first | exact @GlobalTheory.DualCon.good_of_isPullback_finite_surjective | exact GlobalTheory.DualCon.good_of_isPullback_finite_surjective | (intros; apply GlobalTheory.DualCon.good_of_isPullback_finite_surjective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'), (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧ (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  first | exact @GlobalTheory.DualCon.hasRep_baseChange_iff | exact GlobalTheory.DualCon.hasRep_baseChange_iff | (intros; apply GlobalTheory.DualCon.hasRep_baseChange_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualPoint_eq_of_quotient_family_iso : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  first | exact @GlobalTheory.DualCon.inj_of_quotient | exact GlobalTheory.DualCon.inj_of_quotient | (intros; apply GlobalTheory.DualCon.inj_of_quotient <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.CMModel.SqNe

theorem natMul_mem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t) :
    (p : ℂ) * t ∈ L.lattice := by
  have h1 := neg_mem (h.mul _ h.ker)
  rw [← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg] at h1
  exact h1

theorem mul_notMem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t)
    {n : ℕ} (hn : Nat.Coprime n p) : (n : ℂ) * t ∉ L.lattice := fun hm => by
  have h1 := natMul_mem h
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn
  have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e
  have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, e', one_mul] at this
  exact h.notMem this

theorem coprime_sq {p : ℕ} (hp : p.Prime) (k : Sq p) : Nat.Coprime (k.1 : ℕ) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm

theorem sqPt_and_sqProd_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
      (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  intro p F L t hp h4 h3 h
  have h2 : p ≠ 2 := by omega
  refine ⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩
  · have := zsmul_mem (natMul_mem h) (k.1 : ℕ)
    rw [zsmul_eq_mul] at this
    convert this using 1
    rw [sqPt]; push_cast; ring
  · refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]
    have := mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm)
      (coprime_sq hp k))
    intro hm
    apply this
    convert hm using 1
    rw [sqPt]; push_cast; ring

end GlobalTheory.CMModel.SqNe
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem dualNumber_map_flat_surjective : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ ψ : DualNumber k →+* DualNumber K, ψ.comp (dnInl k) = (dnInl K).comp φ ∧ (dnFst K).comp ψ = φ.comp (dnFst k) ∧ Flat (spMap ψ) ∧ Surjective (spMap ψ) := by
  intro k K _ _ φ
  letI : Algebra k K := φ.toAlgebra
  let ψ₀ : DualNumber k →ₐ[k] DualNumber K :=
    DualNumber.lift ⟨(Algebra.ofId k (DualNumber K), DualNumber.eps),
      by simp, fun _ ↦ Commute.all _ _⟩
  have hψ₀ : ∀ x : DualNumber k, ψ₀ x = TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) := by
    intro x
    rw [DualNumber.lift_apply_apply]
    ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let j : K →ₐ[k] DualNumber K := TrivSqZeroExt.inlAlgHom k K K
  let g : TensorProduct k (DualNumber k) K →ₐ[k] DualNumber K :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber K → TensorProduct k (DualNumber k) K := fun x ↦
    (1 : DualNumber k) ⊗ₜ[k] x.fst + (DualNumber.eps : DualNumber k) ⊗ₜ[k] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, g (h x) = x := by
    intro x
    simp only [h, g, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀]
  have hhg : ∀ x, h (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber k) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[k] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective g := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  refine ⟨ψ₀.toRingHom, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [hψ₀, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  · refine RingHom.ext fun x ↦ ?_
    simp [hψ₀]
  · have hc : ψ₀.toRingHom = g.toRingHom.comp (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)) := by
      refine RingHom.ext fun x ↦ ?_
      simp [g, j, Algebra.TensorProduct.algebraMap_apply]
    have hff : (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    have h1 := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)))).2 hff
    have := h1.1
    have := h1.2
    let eR : TensorProduct k (DualNumber k) K ≃+* DualNumber K := (AlgEquiv.ofBijective g hbij).toRingEquiv
    have hi : IsIso (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map eR.toCommRingCatIso.hom))
    rw [hc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.DualOpen
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem milnor_of_ring_square : ∀ (P C₁ C₂ C₀ : Type) [CommRing P] [CommRing C₁] [CommRing C₂] [CommRing C₀] (p₁ : P →+* C₁) (p₂ : P →+* C₂) (q₁ : C₁ →+* C₀) (q₂ : C₂ →+* C₀), q₁.comp p₁ = q₂.comp p₂ → (∀ x, p₁ x = 0 → p₂ x = 0 → x = 0) → (∀ a b, q₁ a = q₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) → Function.Surjective q₂ → Milnor (spMap p₁) (spMap p₂) (spMap q₁) (spMap q₂) := by
  intro P C₁ C₂ C₀ _ _ _ _ p₁ p₂ q₁ q₂ hw hinj hsurj hq₂
  have hwc : CommRingCat.ofHom p₁ ≫ CommRingCat.ofHom q₁ = CommRingCat.ofHom p₂ ≫ CommRingCat.ofHom q₂ := by
    ext x; exact congrArg (fun f : P →+* C₀ => f x) hw
  have H : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom q₁) (CommRingCat.ofHom q₂) := by
    refine IsPullback.of_map (forget CommRingCat) hwc ?_
    rw [Types.isPullback_iff]
    refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hwc], ?_, ?_⟩
    · rintro x y ⟨h1, h2⟩
      have h1' : p₁ x = p₁ y := h1
      have h2' : p₂ x = p₂ y := h2
      exact sub_eq_zero.mp (hinj _ (by rw [map_sub, h1', sub_self]) (by rw [map_sub, h2', sub_self]))
    · intro a b hab
      exact hsurj a b hab
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective _ hq₂, ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, hwc]
  · refine IsPullback.of_iso H (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso _).symm ?_ ?_ ?_ ?_ <;>
    simp [spMap, Scheme.ΓSpecIso_inv_naturality]

end GlobalTheory.DualOpen
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem germ_pull_eq_stalkMap {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

theorem retract_section_apply {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (y : Y) : p (e y) = y := by
  have := congrArg (fun f : Y ⟶ Y ↦ f y) hep
  simpa using this

theorem norm_glue_comm {G : Type} [CommGroup G] (A B F G' R R' : G) (k : A * G' = F * B) :
    A * (G' * R') * (F * R)⁻¹ = B * R' * R⁻¹ := by
  rw [← _root_.mul_assoc, k, mul_inv]
  simp only [_root_.mul_assoc]
  rw [mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]

theorem norm_match_comm {G : Type} [CommGroup G] (A S R R' : G) (h : S = A * R' * R⁻¹) :
    A * S⁻¹ * R' = R := by
  rw [h]; simp only [mul_inv]; simp [mul_comm, mul_left_comm, _root_.mul_assoc]

theorem exists_norm (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (V : Y.Opens)
    (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M)
    (hL : IsOn W₁ L) (hM : IsOn W₂ M) (h₁ : p ⁻¹ᵁ V ≤ W₁) (h₂ : p ⁻¹ᵁ V ≤ W₂)
    (hw : IsoOn (p ⁻¹ᵁ V) L M w) (hr : RigOn e L r) (hr' : RigOn e M r') :
    ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  have hpt := retract_section_apply p e hep
  let O : L.ι × M.ι → Y.Opens := fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))
  have hOV : ∀ i, O i ≤ V := fun i y hy ↦ by
    have : p (e y) ∈ V := hy.1
    rwa [hpt] at this
  have hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1 := fun i y hy ↦ hy.2.1
  have hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2 := fun i y hy ↦ hy.2.2
  have hcov : V ≤ iSup O := fun y hy ↦ by
    have hx : e y ∈ p ⁻¹ᵁ V := show p (e y) ∈ V by rwa [hpt]
    obtain ⟨a, ha⟩ := hL.cov _ (h₁ hx)
    obtain ⟨b, hb⟩ := hM.cov _ (h₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩
  let u : ∀ i, Γ(Y, O i)ˣ := fun i ↦
    pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹
  have hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) =
      gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹ := by
    intro i y hy
    simp only [u, map_mul, map_inv]
    rw [gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V O hOV hcov u (by
    intro i j y hy
    rw [hu i y hy.1, hu j y hy.2]
    obtain ⟨⟨hV, ha, hb⟩, -, ha', hb'⟩ := hy
    have k := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')
    simp only [map_mul, ← germ_pull_eq_stalkMap] at k
    rw [← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩,
      ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩] at k
    rw [hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']
    exact norm_glue_comm _ _ _ _ _ _ k)
  have hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V := fun _ _ ↦ inf_le_left
  refine ⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩
  · intro x hx a a' b b' ha ha' hb hb'
    simp only [map_mul, map_inv]
    rw [gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]
    have k := hw x hx a a' b b' ha ha' hb hb'
    rw [mul_right_comm, k, _root_.mul_assoc]
  · intro y a b hV ha hb
    simp only [map_mul, map_inv]
    have hy : y ∈ O (a, b) := ⟨hV, ha, hb⟩
    rw [gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs,
      hu (a, b) y hy]
    exact norm_match_comm _ _ _ _ rfl

end GlobalTheory.PicGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem glue_into_affineOpen (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) (hM : Milnor j₁.left j₂.left k₁.left k₂.left) (V : U.left.Opens)
    (hV : IsAffineOpen V) (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U) (hk : k₁ ≫ u₁ = k₂ ≫ u₂)
    (h₁ : ∀ x, u₁.left x ∈ V) (h₂ : ∀ x, u₂.left x ∈ V) :
    ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  haveI : IsAffine V.toScheme := hV
  have r₁ : Set.range u₁.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₁ x
  have r₂ : Set.range u₂.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₂ x
  set a₁ := IsOpenImmersion.lift V.ι u₁.left r₁ with ha₁
  set a₂ := IsOpenImmersion.lift V.ι u₂.left r₂ with ha₂
  have f₁ : a₁ ≫ V.ι = u₁.left := IsOpenImmersion.lift_fac _ _ _
  have f₂ : a₂ ≫ V.ι = u₂.left := IsOpenImmersion.lift_fac _ _ _
  have hk' : k₁.left ≫ a₁ = k₂.left ≫ a₂ := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, f₁, f₂]
    exact congrArg CommaMorphism.left hk
  have w : a₁.appTop ≫ k₁.left.appTop = a₂.appTop ≫ k₂.left.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hk']
  set b := hM.cart.lift a₁.appTop a₂.appTop w with hb
  have b₁ : b ≫ j₁.left.appTop = a₁.appTop := hM.cart.lift_fst _ _ _
  have b₂ : b ≫ j₂.left.appTop = a₂.appTop := hM.cart.lift_snd _ _ _
  haveI := hM.aff
  let a : T.left ⟶ V.toScheme := T.left.toSpecΓ ≫ Spec.map b ≫ V.toScheme.isoSpec.inv
  have e₁ : j₁.left ≫ a = a₁ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₁, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e₂ : j₂.left ≫ a = a₂ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₂, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have hover : (a ≫ V.ι) ≫ U.hom = T.hom := by
    apply ext_of_isAffine
    apply hM.cart.hom_ext
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₁, reassoc_of% f₁, Over.w u₁, Over.w j₁]
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₂, reassoc_of% f₂, Over.w u₂, Over.w j₂]
  refine ⟨Over.homMk (a ≫ V.ι) hover, ?_, ?_⟩
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₁, f₁]
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₂, f₂]

end GlobalTheory.DualOpen
end
