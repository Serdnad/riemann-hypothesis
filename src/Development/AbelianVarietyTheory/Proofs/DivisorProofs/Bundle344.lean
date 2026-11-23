module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle268
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCochain_shortExact_of_injective_terms : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  first | exact @GlobalTheory.EtC.cochain_shortExact_of_injective | exact GlobalTheory.EtC.cochain_shortExact_of_injective | (intros; apply GlobalTheory.EtC.cochain_shortExact_of_injective <;> assumption)
end

section

open MeasureTheory Matrix ValuativeRel


theorem _root_.GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  first | exact @GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | exact GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | (intros; apply GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self <;> assumption)
end

section

open GlobalTheory.WeilM
open scoped Matrix

theorem _root_.GlobalTheory.T.siegelUnipotent_antidiagonal_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  first | exact @GlobalTheory.siegel_unip_corner | exact GlobalTheory.siegel_unip_corner | (intros; apply GlobalTheory.siegel_unip_corner <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
instance instWEqLBEtRings (R : Type) [CommRing R] : (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _


set_option backward.isDefEq.respectTransparency false in
theorem etale_affine_of_mem {U : Scheme.{0}} {S : Sieve U} (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S j := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨k, w, hw⟩ := (𝒰.X i).affineCover.exists_eq y
  have hi : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  refine ⟨_, (𝒰.X i).affineCover.f k ≫ 𝒰.f i, w, inferInstance, inferInstance, ?_, S.downward_closed hi _⟩
  rw [Scheme.Hom.comp_apply, hw, hy]

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_loc : ∀ (R : Type) [CommRing R]
    (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}),
    (∀ (x : Sec (ofRings R M) U) (u : U),
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)),
        IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧
    (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U,
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
        IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧
    ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)),
      Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) m 0 (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have := congrArg (fun f => f.hom m) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact this.symm

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

def defect (Q q : ℕ) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  (redMap Q q 1).app U 0 (kumT Q U v) - kumT q U (v ^ (Q / q))

def defectSec (Q q : ℕ) (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  pick fun s => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
    Sec.res g s = defect Q q V v

def corrFam (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 1, s, h, U, x => Sec.map ((res _ (tw q 1)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (defectSec Q q U (lineUnit L x))
  | _, _, _, _, _ => 0

theorem corrFam_zero (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E 0 U) : corrFam Q q L 0 s h U x = 0 := rfl

theorem corrFam_add_two (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : corrFam Q q L (p + 2) s h U x = 0 := rfl

theorem corrFam_one (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : corrFam Q q L 1 0 h U x = defectSec Q q U (lineUnit L x) := by
  simp [corrFam, Sec.map]

end GlobalTheory.EtC.RedChern
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentVarUnit (A : Type) [CommRing A] : (LaurentPolynomial A)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

def laurentVar (A : Type) [CommRing A] : (Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom (laurentVarUnit A)

namespace GmPhi

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

end GmPhi

def gmPhi (q : ℕ) (A : Type) [CommRing A] (i : ℤ) : Ht q (sp A) 0 (i - 1) →+ Ht q (sp (LaurentPolynomial A)) 1 i where
  toFun a := (cup q (pull _ (spMap (LaurentPolynomial.C : A →+* LaurentPolynomial A)) (tw q (i - 1)) 0 a)
    (kum q (laurentVar A))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ofArrows_sigmaι_mem_etale {ι : Type} (V : ι → Scheme.{0}) :
    Presieve.ofArrows V (Sigma.ι V) ∈ Scheme.etalePrecoverage (∐ V) := by
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => inferInstance⟩
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq x
  exact ⟨i, y, hy⟩

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] :
    Subsingleton (Sec F Z) := by
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have hmem : (⊥ : Sieve Z) ∈ Scheme.etaleTopology Z := Scheme.bot_mem_grothendieckTopology (P := @Etale) Z
  refine ⟨fun a b => (hF _ hmem).isSeparatedFor.ext fun _ _ hf => ?_⟩
  simp at hf

theorem sec_sigma_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  intro R _ F ι V
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have h := hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck (ofArrows_sigmaι_mem_etale V))
  rw [Presieve.isSheafFor_arrows_iff] at h
  have hc : ∀ x : ∀ i, Sec F (V i), Presieve.Arrows.Compatible (F.obj ⋙ forget _) (Sigma.ι V) x := by
    intro x i j Z gi gj hij
    by_cases e : i = j
    · subst e
      obtain rfl := (cancel_mono (Sigma.ι V i)).1 hij
      rfl
    · have : IsEmpty Z := ⟨fun z => (isEmpty_pullback_sigmaι_of_ne V e).false ((pullback.lift gi gj hij).base z)⟩
      have := sec_subsingleton_of_isEmpty F Z
      exact Subsingleton.elim _ _
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · obtain ⟨t, -, ht⟩ := h (fun i => Sec.res (Sigma.ι V i) a) (hc _)
    exact (ht a fun i => rfl).trans (ht b fun i => (congrFun hab i).symm).symm
  · obtain ⟨t, ht, -⟩ := h x (hc x)
    exact ⟨t, funext ht⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open Polynomial in
theorem prim_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  intro q A _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let k := IsLocalRing.ResidueField A
  have hqk : IsUnit ((q : ℕ) : k) := by
    have := hq.map (IsLocalRing.residue A)
    rwa [map_natCast] at this
  haveI : NeZero ((q : ℕ) : k) := ⟨hqk.ne_zero⟩
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hqk
    · exact h
  have hsepk : (cyclotomic q k).Separable := separable_cyclotomic q k
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (cyclotomic q k)
    (degree_cyclotomic_pos q k hq0).ne' hsepk
  have hmap : (cyclotomic q A).map (algebraMap A k) = cyclotomic q k := map_cyclotomic q _
  have h1 : aeval a₀ (cyclotomic q A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]; exact ha₀
  have h2 : aeval a₀ (derivative (cyclotomic q A)) ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, hmap]
    have := hsepk.aeval_derivative_ne_zero (x := a₀) (by simpa [aeval_def] using ha₀)
    simpa [aeval_def] using this
  have hT := (HenselianLocalRing.TFAE A).out 1 2
  obtain ⟨a, ha, -⟩ := hT.mp hH (cyclotomic q A) (cyclotomic.monic q A) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  have : (cyclotomic q ℤ).map (Int.castRingHom A) = cyclotomic q A := map_cyclotomic q _
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, this]
  exact ha

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NatFamExt

variable {R : Type} [CommRing R] (P : PSh)

def finMap {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) :
    (P.obj V →₀ F.obj V) →ₗ[ULift.{1} R] (P.obj W →₀ F.obj W) :=
  Finsupp.lmapDomain (F.obj W) (ULift.{1} R) (P.map g) ∘ₗ Finsupp.mapRange.linearMap (F.map g).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] (P : _root_.GlobalTheory.EtC.PSh) in
theorem _root_.GlobalTheory.NatFamExt.finMap_single {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : P.obj V) (a : F.obj V) :
    _root_.GlobalTheory.NatFamExt.finMap P g (Finsupp.single x a) =
      Finsupp.single (P.map g x) ((F.map g).hom a) := by
  simp [_root_.GlobalTheory.NatFamExt.finMap, Finsupp.mapDomain_single]

def finP (F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ (P.obj V →₀ F.obj V)
  map g := ModuleCat.ofHom (finMap P g)
  map_id V := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (𝟙 V) (Finsupp.single x a) = Finsupp.single x a
    rw [finMap_single]
    simp
  map_comp f g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (f ≫ g) (Finsupp.single x a) = finMap P g (finMap P f (Finsupp.single x a))
    rw [finMap_single, finMap_single, finMap_single]
    simp

def finPMap {F F' : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ F') : finP P F ⟶ finP P F' where
  app V := ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.app V).hom)
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.mapRange.linearMap (φ.app W).hom (finMap P g (Finsupp.single x a)) =
      finMap P g (Finsupp.mapRange.linearMap (φ.app V).hom (Finsupp.single x a))
    rw [finMap_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, finMap_single]
    exact congrArg _ (congrArg (fun h => h.hom a) (φ.naturality g))

def famHom (G : Shv R) {A : Shv R} (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V)
    (hψ : ∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V),
      Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) :
    finP P A.obj ⟶ G.obj where
  app V := ModuleCat.ofHom (Finsupp.lsum (ULift.{1} R) (ψ V.unop))
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.lsum (ULift.{1} R) (ψ W.unop) (finMap P g (Finsupp.single x a)) =
      (G.obj.map g).hom (Finsupp.lsum (ULift.{1} R) (ψ V.unop) (Finsupp.single x a))
    rw [finMap_single, Finsupp.lsum_single, Finsupp.lsum_single]
    exact (hψ _ _ g.unop x a).symm

end GlobalTheory.NatFamExt

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.natFam_extend_of_injective : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (G : _root_.GlobalTheory.EtC.Shv R), Injective G → ∀ {A B : _root_.GlobalTheory.EtC.Shv R} (f : A ⟶ B), Mono f →
    ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec A V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V),
    (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
      _root_.GlobalTheory.EtC.Sec.res w (ψ V x a) = ψ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w a)) →
    ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec B V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V,
      (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : _root_.GlobalTheory.EtC.Sec B V),
        _root_.GlobalTheory.EtC.Sec.res w (χ V x b) = χ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w b)) ∧
      ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
        χ V x (_root_.GlobalTheory.EtC.Sec.map f a) = ψ V x a := by
  intro R _ P G hG A B f hf ψ hψ
  have hfval : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have hinj : ∀ V, Function.Injective (f.hom.app V).hom := fun V =>
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f.hom).1 hfval V)
  haveI : Injective G.obj :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology _) G
  haveI : Mono (_root_.GlobalTheory.NatFamExt.finPMap P f.hom) := by
    rw [NatTrans.mono_iff_mono_app]
    intro V
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) (hinj V)
  obtain ⟨θ, hθ⟩ := Injective.factors (_root_.GlobalTheory.NatFamExt.famHom P G ψ hψ)
    (_root_.GlobalTheory.NatFamExt.finPMap P f.hom)
  refine ⟨fun V x => (θ.app (op V)).hom ∘ₗ Finsupp.lsingle x, ?_, ?_⟩
  · intro V W w x b
    have h := congrArg (fun h => h.hom (Finsupp.single x b)) (θ.naturality w.op)
    change (θ.app (op W)).hom (_root_.GlobalTheory.NatFamExt.finMap P w.op (Finsupp.single x b)) =
      (G.obj.map w.op).hom ((θ.app (op V)).hom (Finsupp.single x b)) at h
    rw [_root_.GlobalTheory.NatFamExt.finMap_single] at h
    exact h.symm
  · intro V x a
    have h := congrArg (fun h => (h.app (op V)).hom (Finsupp.single x a)) hθ
    change (θ.app (op V)).hom
        (Finsupp.mapRange.linearMap (f.hom.app (op V)).hom (Finsupp.single x a)) =
      Finsupp.lsum (ULift.{1} R) (ψ V) (Finsupp.single x a) at h
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.lsum_single] at h
    exact h
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.PrimColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

theorem nat_apply {j k : J} (f : j ⟶ k) (a : D.obj j) :
    (c.ι.app k).hom ((D.map f).hom a) = (c.ι.app j).hom a := by
  rw [← c.w f]; rfl

theorem exists_rep (hc : IsColimit c) (x : c.pt) : ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, h⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, h⟩

theorem exists_eq (hc : IsColimit c) {j : J} (a b : D.obj j) (h : (c.ι.app j).hom a = (c.ι.app j).hom b) :
    ∃ (k : J) (f : j ⟶ k), (D.map f).hom a = (D.map f).hom b := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc a b h
  refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom a = (D.map g).hom b := hfg
  have e := IsFiltered.coeq_condition f g
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom a
      = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom a) := by rw [D.map_comp]; rfl
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom b) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom b := by rw [D.map_comp]; rfl
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom b := by rw [e]

theorem aeval_ringHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) (p : Polynomial ℤ) :
    Polynomial.aeval (φ a) p = φ (Polynomial.aeval a p) :=
  Polynomial.aeval_algHom_apply φ.toIntAlgHom a p

end GlobalTheory.EtC.PrimColim

open GlobalTheory.EtC.PrimColim in
theorem GlobalTheory.EtC.prim_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  intro q J _ _ D c hc
  refine ⟨fun ζ => ?_, fun j ξ ξ' h => ?_⟩
  · obtain ⟨u, hu⟩ := ζ.2.1.exists_right_inv
    obtain ⟨j1, x, hx⟩ := exists_rep hc ζ.1
    obtain ⟨j2, y, hy⟩ := exists_rep hc u
    set k := IsFiltered.max j1 j2
    set x' := (D.map (IsFiltered.leftToMax j1 j2)).hom x
    set y' := (D.map (IsFiltered.rightToMax j1 j2)).hom y
    have hx' : (c.ι.app k).hom x' = ζ.1 := by rw [nat_apply, hx]
    have hy' : (c.ι.app k).hom y' = u := by rw [nat_apply, hy]
    have e1 : (c.ι.app k).hom ((q : D.obj k) * y') = (c.ι.app k).hom 1 := by
      rw [map_mul, map_natCast, hy', map_one, hu]
    obtain ⟨k1, f1, hf1⟩ := exists_eq hc _ _ e1
    set x1 := (D.map f1).hom x'
    have hx1 : (c.ι.app k1).hom x1 = ζ.1 := by rw [nat_apply, hx']
    have e2 : (c.ι.app k1).hom (Polynomial.aeval x1 (Polynomial.cyclotomic q ℤ)) = (c.ι.app k1).hom 0 := by
      rw [map_zero, ← aeval_ringHom, hx1]; exact ζ.2.2
    obtain ⟨k2, f2, hf2⟩ := exists_eq hc _ _ e2
    have hu1 : (q : D.obj k1) * (D.map f1).hom y' = 1 := by
      simpa only [map_mul, map_natCast, map_one] using hf1
    have hu2 : (q : D.obj k2) * (D.map f2).hom ((D.map f1).hom y') = 1 := by
      have := congrArg (D.map f2).hom hu1
      simpa only [map_mul, map_natCast, map_one] using this
    have hr : Polynomial.aeval ((D.map f2).hom x1) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [aeval_ringHom, hf2, map_zero]
    refine ⟨k2, ⟨(D.map f2).hom x1, IsUnit.of_mul_eq_one _ hu2, hr⟩, ?_⟩
    apply Subtype.ext
    change (c.ι.app k2).hom ((D.map f2).hom x1) = ζ.1
    rw [nat_apply, hx1]
  · have h1 : (c.ι.app j).hom ξ.1 = (c.ι.app j).hom ξ'.1 := congrArg Subtype.val h
    obtain ⟨k, f, hf⟩ := exists_eq hc _ _ h1
    exact ⟨k, f, Subtype.ext hf⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

def HInv (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Prop :=
  ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

end GlobalTheory.EtC
end
