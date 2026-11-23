module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle471
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle450
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisDP

theorem wn_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ),
    IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  intro l _ K r n
  let F₀ : WittVector l r.k →+* (base l).Acr0 :=
    (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))
  refine RL.pd_mor (Ideal.Quotient.mk _) ((base l).mkAcr n) (Ideal.span {(l : WittVector l r.k)}) (base l).PFil0
    (Wc.pd l r.k n) (B.DD true (base l) n) F₀ (Mid.wn r n) Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) ((base l).isPd_pdPFil n) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  · intro a
    rw [Mid.wn_mk]
    exact (base l).cris_algebraMap n (WittVector.map r.s a)

end GlobalTheory.CompanionTheory.CrisDP
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisFlat

theorem flat_quotient_of_flat {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) (f : R ⧸ I →+* A ⧸ J)
    (hf : ∀ a, f (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap R A a)) :
    letI := f.toAlgebra; Module.Flat (R ⧸ I) (A ⧸ J) := by
  subst hJ
  letI := f.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  let e₀ : (R ⧸ I) ⊗[R] A ≃ₗ[R] A ⧸ I.map (algebraMap R A) :=
    (TensorProduct.comm R (R ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.restrictScalars R)
  let e : (R ⧸ I) ⊗[R] A ≃ₗ[R ⧸ I] A ⧸ I.map (algebraMap R A) :=
    e₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact Module.Flat.of_linearEquiv e.symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def wToAcr0 (r : Res l K) : WittVector l r.k →+* (base l).Acr0 :=
  (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))

theorem isTorsionFree_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.IsTorsionFree (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x h
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' a ha
  rw [Algebra.smul_def] at h
  have h1 : (wToAcr0 r a : Localization.Away (l : (base l).W)) * (x : Localization.Away (l : (base l).W)) = 0 :=
    congrArg Subtype.val h
  have hl : IsUnit (l : Localization.Away (l : (base l).W)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : (base l).W)) (l : (base l).W)
    rwa [map_natCast] at this
  have hu : IsUnit (wToAcr0 r a : Localization.Away (l : (base l).W)) := by
    have e2 : (wToAcr0 r a : Localization.Away (l : (base l).W)) =
        (l : Localization.Away (l : (base l).W)) ^ m * ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) b := by
      change ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) a = _
      rw [e, map_mul, map_pow, map_natCast]
    rw [e2]
    exact (hl.pow m).mul (b.isUnit.map _)
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h1)

theorem flat_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.Flat (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  haveI := isTorsionFree_acris_zero r
  infer_instance

theorem flat_acr (r : Res l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  letI := (wToAcr0 r).toAlgebra
  haveI := flat_acris_zero r
  refine flat_quotient_of_flat (R := WittVector l r.k) (A := (base l).Acr0)
    (Ideal.span {(l : WittVector l r.k) ^ n}) (Ideal.span {(l : (base l).Acr0) ^ n}) ?_ (Mid.wn r n) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · intro a
    exact (Mid.wn_mk r n a).trans ((base l).cris_algebraMap n (WittVector.map r.s a))

end GlobalTheory.CompanionTheory.CrisFlat
end
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.smooth_model_restriction_bijective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ m j, Function.Bijective (resF l (B.schFn M.p) r.ρ m j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatRes.flat_restriction | exact GlobalTheory.CompanionTheory.FlatRes.flat_restriction | (intros; apply GlobalTheory.CompanionTheory.FlatRes.flat_restriction <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.flat_witt_tower_level : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  first | exact @GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | exact GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | (intros; apply GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

theorem cmpq_bijective (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ) : Function.Bijective ((cmpq A l n).f i) := by
  have hmk := cmpq_mk A l n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hmk] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))),
        a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s := by
      intro s
      have h1 : ((qM A l n).pullC i y) s = 0 := by
        rw [hq]
        rfl
      have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0 :=
        congrArg Subtype.val h1
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    choose a ha using hy
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    refine ⟨a, ?_⟩
    funext s
    show ((l : R) ^ n) • a s = y s
    rw [Algebra.smul_def, mul_comm]
    exact ha s
  · intro g
    have hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))),
        Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x =
          Subtype.val (g s) := fun s => Ideal.Quotient.mk_surjective _
    choose x hx using hx
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hmk]
    funext s
    apply Subtype.ext
    exact hx s

end GlobalTheory.CompanionTheory.LsCmp

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.FlatThick


open TensorProduct in
set_option backward.isDefEq.respectTransparency true in
theorem flat_quotientMap {P B : Type} [CommRing P] [CommRing B] [Algebra P B] [Module.Flat P B] (I₀ : Ideal P) :
    (Ideal.quotientMap (I₀.map (algebraMap P B)) (algebraMap P B) Ideal.le_comap_map :
      P ⧸ I₀ →+* B ⧸ I₀.map (algebraMap P B)).Flat := by
  have f3 : (algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let e₂ : (B ⧸ I₀.map (algebraMap P B)) ≃+* (P ⧸ I₀) ⊗[P] B :=
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).toRingEquiv).trans
        (Algebra.TensorProduct.comm P B (P ⧸ I₀)).toRingEquiv)
  have f5 : (e₂.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₂.symm.bijective
  have f4 := RingHom.Flat.comp f3 f5
  convert f4 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  refine e₂.injective ?_
  have : e₂ (Ideal.Quotient.mk _ (algebraMap P B r)) = algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B) (Ideal.Quotient.mk _ r) := by
    change Algebra.TensorProduct.comm P B (P ⧸ I₀) (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀ (Ideal.Quotient.mk _ (algebraMap P B r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  simpa using this

theorem flat_of_surjective_ker {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (π : A →+* A') (hπ : Function.Surjective π) (a : A) (hker : RingHom.ker π = Ideal.span {a})
    (g : A' →+* B ⧸ Ideal.span {f a}) (hg : ∀ r, g (π r) = Ideal.Quotient.mk _ (f r)) : g.Flat := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hJ : (Ideal.span {a}).map (algebraMap A B) = Ideal.span {f a} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let e₁ : (A ⧸ Ideal.span {a}) ≃+* A' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₂ : (B ⧸ (Ideal.span {a}).map (algebraMap A B)) ≃+* (B ⧸ Ideal.span {f a}) := Ideal.quotEquivOfEq hJ
  have h0 := flat_quotientMap (P := A) (B := B) (Ideal.span {a})
  have h1 : (e₁.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₁.symm.bijective
  have h2 : (e₂.toRingHom).Flat := RingHom.Flat.of_bijective e₂.bijective
  have h3 := RingHom.Flat.comp (RingHom.Flat.comp h1 h0) h2
  convert h3 using 1
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := hπ x
  have hr : e₁.symm (π r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change g (π r) = e₂ (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map (e₁.symm (π r)))
  rw [hr, hg]
  rfl

theorem flatT_qT (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O]
    (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) (hT : FlatT T) :
    FlatT (qT hn T) := by
  refine flat_of_surjective_ker T.i hT (Wc.red l k n) ?_ (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n)) ?_ (qi T)
    (qi_red T)
  · intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, red_mk' w⟩
  · ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, red_mk', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Ideal.Quotient.mk _ c, (map_mul _ _ _)⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨c + (l : WittVector l k) * d, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ, ← hd]
      ring

end GlobalTheory.CompanionTheory.FlatThick

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatCoverGlue



theorem glue {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k)
    (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c))
    (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory),
      stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj)
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j)) (j : ℕ) :
    Function.Bijective
      (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  have hGU : ∀ (α : U.ι) (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory), InU (U.U α) T.obj →
      InU (U.U α) (m.G.obj ⟨T.obj, T.property.1⟩).obj := fun α T hT => by
    obtain ⟨-, V, rfl, hV⟩ := hG {U.U α} ⟨T.obj, T.property.1, U.U α, rfl, hT⟩
    exact hV
  refine cover_bij ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
      (IdF.span _ c) (fun _ => le_rfl))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => hGU α T hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁ : ∀ (r : ℕ) T, stF q ρ r {⨅ α ∈ S, U.U α} T →
      ∃ hp : stF q ρ r (Set.range U.U) T,
        capS (fun α (T : (stF q ρ r (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun r T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have a₀ := nestAdj (h₁ n) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have a₁ := nestAdj (h₁ (n + 1)) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (stF q ρ n (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sV q ρ n (Set.range U.U)).A) (CH.modF (sV q ρ n {⨅ α ∈ S, U.U α}).A) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ n))
  let rO : CH.Mor ((capS (fun α (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sV q ρ (n + 1) (Set.range U.U)).A) (IdF.span (sV q ρ (n + 1) (Set.range U.U)).A c))
      (sq (IdF.top (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A) (IdF.span (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A c)) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ (n + 1)))
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₀ j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₁ j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x) =
      ((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id _) _ _ (𝟙 _) (fun T y => ?_) j x
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end GlobalTheory.CompanionTheory.FlatCoverGlue
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl


theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.archimedean_character_real_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.JSPair.exists_pairing | exact GlobalTheory.CompanionTheory.JSPair.exists_pairing | (intros; apply GlobalTheory.CompanionTheory.JSPair.exists_pairing <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.annihilator_adelic_lattice_compact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ}, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)), (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) → (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) → ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | exact GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | (intros; apply GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.exists_char_twist_cuspidal_lie_eigenvalue_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ, ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))), IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → lie E a (oneL E a) φ = c • φ → mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspTwist.twist_central | exact GlobalTheory.CompanionTheory.CuspTwist.twist_central | (intros; apply GlobalTheory.CompanionTheory.CuspTwist.twist_central <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem cofin_monic_on_killed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ n J hJ z hz => GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E n J hJ z hz

end GlobalTheory.CompanionTheory.CTFin
end
