module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Mathlib.NumberTheory.Padics.Complex
import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle445
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.FinProjComplete

theorem smodEq_span_singleton_pow_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, x - y = a ^ n • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, hz⟩; exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩; exact ⟨z, Submodule.mem_top, hz.symm⟩

end GlobalTheory.FinProjComplete

namespace GlobalTheory.FinProjComplete

theorem isAdicComplete_of_finite_projective : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective <;> assumption

end GlobalTheory.FinProjComplete
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_cochain_ev_eq_of_natural' :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
      (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  apply GlobalTheory.EtC.exists_cochain_ev_eq_of_natural <;> assumption
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_eq_δ (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  apply GlobalTheory.EZ.fc_succ_eq_delta <;> assumption

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom, SimplexCategory.mkHom]
  omega

theorem hsum_f {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {α : Type} (s : Finset α) (f : α → (K ⟶ L)) (i : ι) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  (HomologicalComplex.eval C c i).map_sum f s

section
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem dbl_d_f (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).d (a + 1) a).f b = (ev Y).map (dH (a + 1) b a b) := by

  simp only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
  idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Finset.sum_range]
  dsimp only [dbl, alternatingFaceMapComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, hsum_f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.zsmul_f_apply, fc_eq_δ]
  rfl

theorem dbl_X_d (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).X a).d (b + 1) b = (ev Y).map (dV a (b + 1) a b) := by

  simp only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
  idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [Finset.sum_range]
  change (AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fc_eq_δ]
  rfl

variable [HasFiniteCoproducts C]

theorem ιTotal_D₁ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₁ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dH a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  rw [HomologicalComplex₂.ι_D₁]
  rcases a with _ | a
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2) := by omega
    simp only [dH, hx, if_false, Functor.map_zero]
    exact zero_comp
  · rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_d_f]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a + 1 = x1 + 1 ∧ b = x2) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h2
        have : x1 = a := by omega
        subst this
        rfl
      simp only [dH, this, if_false, Functor.map_zero]
      exact zero_comp
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_D₂ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₂ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, ((-1 : ℤ) ^ a) • ((ev Y).map (dV a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)) := by
  rw [HomologicalComplex₂.ι_D₂]
  rcases b with _ | b
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1) := by omega
    simp only [dV, hx, if_false, Functor.map_zero]
    exact (congrArg _ zero_comp).trans (zsmul_zero _)
  · rw [HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_X_d]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a = x1 ∧ b + 1 = x2 + 1) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h1
        have : x2 = b := by omega
        subst this
        rfl
      simp only [dV, this, if_false, Functor.map_zero]
      exact (congrArg _ zero_comp).trans (zsmul_zero _)
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_tot_d (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ)
    (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (tot Y).d (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  change _ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]
  refine Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))
  rw [dT, (ev Y).map_add, (ev Y).map_zsmul]
  first
    | (rw [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (simp only [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (erw [Preadditive.add_comp, Preadditive.zsmul_comp])
  rfl

end

end GlobalTheory.EZ
end
end

section

namespace GlobalTheory.IntegralNormAtMostOne

theorem norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.MomOne.model_norm_le_one_of_isIntegral <;> assumption

end GlobalTheory.IntegralNormAtMostOne
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.MonoEpi

instance wEqLBMonoEpi (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {R : Type} [CommRing R]

theorem sec_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h (unop U) a

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := inferInstanceAs (Mono ((sheafToPresheaf _ _).map φ))
    have : Mono (φ.hom.app (op U)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (ModuleCat.mono_iff_injective _).2 (h (unop U))
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  apply LateralTheory.EtaleFoundations.MonoEpiPf.inj_iff_loc <;> assumption

theorem epi_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h U b
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology φ.hom b, fun V g hg => hg⟩
  · intro h
    constructor
    intro U b
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    exact hP V g hg

end GlobalTheory.EtC.MonoEpi

open GlobalTheory.EtC.MonoEpi in
theorem GlobalTheory.EtC.mono_epi_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff_loc φ, fun ψ h => sec_ext φ ψ h⟩
end

section

namespace GlobalTheory.TargetLemmaCollection

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

end GlobalTheory.TargetLemmaCollection

theorem GlobalTheory.TargetLemmaCollection.target : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
end

section


theorem _root_.GlobalTheory.T.lipschitz_formula_totally_real_poisson : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_bC_eq_range_alC_and_ker_alC_eq_range_bC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (h : ℕ) (D : Datum ε h Γ), LinearMap.ker (bC C D) = LinearMap.range (alC C D) ∧ LinearMap.ker (alC C D) = LinearMap.range (bC C D) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ h D
  obtain ⟨hdom, -, hker, hsurj, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  have hFG : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    (GlobalTheory.DetInv.datum_scalar_intertwine p C v O hv ε hε Γ h D).2.1
  have hGF : D.G * D.F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := D.G_mul_F
  set f : Ainf p O →+* C := (algebraMap O C).comp (WittVector.fontaineTheta O p) with hf
  have hinj := hv.hom_inj
  have hfnu : f (nu ε) ≠ 0 := by
    intro h0
    apply hnu
    apply hinj
    simpa [hf] using h0
  have hxiker : WittVector.fontaineTheta O p (xi ε) = 0 := by
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    exact this
  have hfmu : f (mu ε) = 0 := by
    rw [← xi_mul_nu, map_mul]
    simp [hf, hxiker]
  have hnzd : xi ε ∈ nonZeroDivisors (Ainf p O) := mem_nonZeroDivisors_of_ne_zero hxi
  have hfrac : ∀ c : C, ∃ s t : Ainf p O, f s ≠ 0 ∧ c * f s = f t := by
    intro c
    by_cases hc : v c ≤ 1
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one hc
      obtain ⟨t, rfl⟩ := hsurj a
      refine ⟨1, t, by simp, ?_⟩
      simp [hf, ha]
    · have hc0 : c ≠ 0 := by
        intro h0; apply hc; simp [h0]
      have hle : v c⁻¹ ≤ 1 := by
        rw [map_inv₀]
        push_neg at hc
        exact inv_le_one_of_one_le₀ hc.le
      obtain ⟨a, ha⟩ := hv.exists_of_le_one hle
      obtain ⟨s, rfl⟩ := hsurj a
      refine ⟨s, 1, ?_, ?_⟩
      · simp [hf, ha, hc0]
      · simp [hf, ha, hc0]
  have hdiv : ∃ s : Ainf p O, f s ≠ 0 ∧ ∀ r : Ainf p O, f r = 0 → xi ε ∣ s * r := by
    refine ⟨1, by simp, fun r hr => ?_⟩
    have h1 : WittVector.fontaineTheta O p r = 0 := by
      apply hinj; simpa [hf] using hr
    have h2 : r ∈ RingHom.ker (WittVector.fontaineTheta O p) := h1
    rw [hker, Ideal.mem_span_singleton] at h2
    simpa using h2
  have hmuxi : mu ε = xi ε * nu ε := (xi_mul_nu ε).symm

  have hcomp : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = mu ε • 1 →
      ∀ z : Fin h → C, X.map f *ᵥ (Y.map f *ᵥ z) = 0 := by
    intro X Y hXY z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hXY]
    have : (mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))).map f = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply, hfmu]
    rw [this, Matrix.zero_mulVec]
  have hb : ∀ z, bC C D z = D.G.map f *ᵥ z := fun z => by
    simp [bC, redC, Matrix.toLin'_apply, hf]
  have ha : ∀ z, alC C D z = D.F.map f *ᵥ z := fun z => by
    simp [alC, redC, Matrix.toLin'_apply, hf]
  constructor
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, hb] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.G D.F
        hnzd hfnu hfrac hdiv (by rw [hFG, hmuxi]) x hx
      exact ⟨y, by rw [ha, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.G D.F hGF y
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, ha] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.F D.G
        hnzd hfnu hfrac hdiv (by rw [hGF, hmuxi]) x hx
      exact ⟨y, by rw [hb, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.F D.G hFG y

end GlobalTheory.DetInv
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  first | exact @GlobalTheory.HeckeTwo.summable_eisClass_two | exact GlobalTheory.HeckeTwo.summable_eisClass_two | (intros; apply GlobalTheory.HeckeTwo.summable_eisClass_two <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory


theorem _root_.GlobalTheory.T.eq_of_agree_on_affineOpen_generators : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens), IsAffineOpen N → ∀ (m : ℕ) (r : Fin m → Γ(X, N)), (∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) → ∀ (a b : W ⟶ X), a ≫ sm = b ≫ sm → ∀ (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N), (∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) = (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) → a = b := by
  first | exact @GlobalTheory.eq_of_agree_on_generators | exact GlobalTheory.eq_of_agree_on_generators | (intros; apply GlobalTheory.eq_of_agree_on_generators <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne g w N F F' hN hF hq

  rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
end
