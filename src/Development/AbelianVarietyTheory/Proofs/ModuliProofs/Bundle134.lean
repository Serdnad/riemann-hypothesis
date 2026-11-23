module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMemVanIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.ThIdeal

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  apply GlobalTheory.ZM.TObj.HasTh.unit_mul <;> assumption

theorem coeff_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have hm : MvPolynomial.monomial d c ∈ MvPolynomial.homogeneousSubmodule σ R d.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    have : MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (MvPolynomial.monomial d c) =
        Polynomial.C (MvPolynomial.eval₂Hom β w (MvPolynomial.monomial d c)) * Polynomial.X ^ d.degree := by
      simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, Finsupp.degree_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem component_eq_zero {R σ : Type} [CommRing R] (β : R →+* ℂ) (w : σ → ℂ)
    (F : MvPolynomial σ R) (e : ℕ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂Hom β (fun i => c * w i) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_scale]
  have : MvPolynomial.eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) (fun c hc => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl
    have h1 := MvPolynomial.map_eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (Polynomial.evalRingHom c) F
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom, h1, ← h c hc]
    congr 2
    · ext r; simp
    · ext i; simp [_root_.mul_comm c]
  rw [this, Polynomial.coeff_zero]

theorem mem_thIdeal {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} (em : o →+* ℂ)
    (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (F : MvPolynomial (Ix g (N' ^ 2)) o) :
    F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v → MvPolynomial.eval₂Hom em v F = 0 := by
  simp only [thIdeal, Ideal.mem_iInf, RingHom.mem_ker, and_imp]

theorem thIdeal_radical_homogeneous_torsionFree :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  intro o _ g N' J b em C hem
  refine ⟨fun F hF => ?_, fun F hF e => ?_, fun c F hc hF => ?_⟩
  · obtain ⟨n, hn⟩ := hF
    rw [mem_thIdeal] at hn ⊢
    intro t v ht hv
    have := hn t v ht hv
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    exact component_eq_zero em v F e fun c hc => hF t _ ht (hasTh_unit_mul hv c hc.isUnit)
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    have := hF t v ht hv
    rw [map_mul, MvPolynomial.eval₂Hom_C] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero_iff em hem).mpr hc)

end GlobalTheory.ZM.ThIdeal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FlatFamily


open MvPolynomial in
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
  have hh : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro G ⟨hG, -⟩
    exact ⟨d, (mem_homogeneousSubmodule d G).2 hG⟩
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem (h := hh) (p := F)).1 hF e


open MvPolynomial in
theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  apply GlobalTheory.ZM.NearCut.eval₂_eq_zero_of_forms_le <;> assumption

theorem exists_flat_projRep_vanIdeal : ∀ (R σ Hh : Type) [CommRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), Ideal (MvPolynomial σ K) → Prop), (∀ (K : Type) [Field K] (x : R →+* K) I, G K x I → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p h i))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : _), RingHom.ker x = q ∧ G K x I} → ∃ (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d p) Z.hom M th ∧ IsProjOver Z.hom ∧ Flat Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), G K x I → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ p Q d G hG hVD
  classical
  have bc : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := fun R R' σ _ _ φ I Z Z' s s' π M th h hpb => RepBC.projRep_baseChange R R' σ φ I Z Z' s s' π M th h hpb
  obtain ⟨hproj, hfg, hbase⟩ := GlobalTheory.FamAlg.forms_through_points R σ Hh p Q d _ hVD (by
    rintro q ⟨K, _, x, I, rfl, hGx⟩
    exact ⟨K, _, x, I, rfl, (hG K x I hGx).2⟩)
  have hhom : ∀ F ∈ vanIdeal d p, ∀ e, MvPolynomial.homogeneousComponent e F ∈ vanIdeal d p :=
    fun F hF e => homogeneousComponent_mem_vanIdeal d p F hF e
  obtain ⟨Z₀, s, M, th, -, hrep, hlfp, hflat⟩ := GlobalTheory.ProjFlat.exists_projRep_flat R σ (vanIdeal d p) d hhom
  have hZ := GlobalTheory.ZM.projRep_projective_ample R σ (vanIdeal d p) (Over.mk s) M th hrep
  refine ⟨Over.mk s, M, th, hrep, hZ.1, hflat (fun e he => by haveI := hproj e he; infer_instance), hlfp hfg, ?_⟩
  intro K _ x I' X s' M' th' hGx hrep'
  obtain ⟨hI'hom, hcut⟩ := hG K x I' hGx
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hsec₁⟩ := bc R K σ x (vanIdeal d p) Z₀ (pullback s (spMap x)) s
    (pullback.snd s (spMap x)) (pullback.fst s (spMap x)) M th hrep hpb
  rw [hbase K x] at hrep₁
  have heqv : ∀ (R' : Type) [CommRing R'] (β : K →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ →
      ((∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) ↔
        ∀ F ∈ vanIdeal d (fun h i => x (p h i)), MvPolynomial.eval₂ β v F = 0) := by
    intro R' _ β v hv
    constructor
    · intro h
      exact eval₂_eq_zero_of_forms_le (fun F hF e => homogeneousComponent_mem_vanIdeal d _ F hF e)
        (fun e he F hFe hF => ((hcut e he).2 F hFe).2 hF) β v hv h
    · intro h
      exact eval₂_eq_zero_of_forms_le hI'hom (fun e he F hFe hF => ((hcut e he).2 F hFe).1 hF) β v hv h
  obtain ⟨e, hes, hlb, hsc⟩ := GlobalTheory.RepUniq.exists_iso_of_projRep K σ I' _ X _ s' _ M' _ th' th₁ hrep' hrep₁ heqv
  have hsc' : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ e.hom ≫ pullback.fst s (spMap x)) w := by
    intro T _ y w
    rw [hsc, hsec₁, Category.assoc]
  have hsame : GlobalTheory.RepUniq.Same M' th' (𝟙 X) M th (e.hom ≫ pullback.fst s (spMap x)) := by
    refine GlobalTheory.RepUniq.same_of_local fun t => ?_
    obtain ⟨W, hW, j, hj, htW, hW'⟩ := GlobalTheory.RepUniq.exists_affine_secCoord hrep'.1 th' (𝟙 X) t
    refine ⟨W, htW, ?_⟩
    have h1 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep'.1 hW'
    have h2 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep.1 ((hsc' _ _ _).1 hW')
    have h3 := (h1.same h2).comp hW.isoSpec.hom
    have h4 : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := GlobalTheory.RepUniq.isoSpec_hom_fromSpec hW
    simp only [Category.comp_id, ← Category.assoc, h4] at h3 ⊢
    exact h3
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, GlobalTheory.RepUniq.lbIso_of_same hrep' hsame, hsc'⟩
  · have sq1 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hes, Category.comp_id]⟩
    simpa using sq1.paste_horiz hpb

end GlobalTheory.ZM.FlatFamily
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem image_inf_le {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (U V : Z'.Opens) :
    f ''ᵁ U ⊓ f ''ᵁ V ≤ f ''ᵁ (U ⊓ V) := by

  rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
  obtain rfl : b = a := f.isOpenEmbedding.injective hba
  exact ⟨b, ⟨ha, hb⟩, rfl⟩

def pushLB {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') : LB Z :=
  ⟨A.ι, fun i => f ''ᵁ A.U i, fun i j => res (image_inf_le f (A.U i) (A.U j))
    (Units.map (f.appIso (A.U i ⊓ A.U j)).inv.hom.toMonoidHom (A.g i j))⟩

def sumLB {Z : Scheme.{0}} (A B : LB Z) : LB Z :=
  ⟨A.ι ⊕ B.ι, Sum.elim A.U B.U, fun p q => match p, q with
    | .inl i, .inl j => A.g i j
    | .inr i, .inr j => B.g i j
    | .inl _, .inr _ => 1
    | .inr _, .inl _ => 1⟩

def AmpleFam {Z : Scheme.{0}} (A : LB Z) : Prop :=
  ∀ z : Z, ∃ (d : ℕ) (s : H0 A d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

def HasFrames {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n : ℕ) (r s : ℤ) : Prop :=
  ∃ (th : ∀ i : A.ι, LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk (A.U i).ι)))
    (b : ∀ i : A.ι, Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (A.U i).ι))),
  (∀ i j : A.ι, ∃ (c : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((A.U i ⊓ A.U j).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => th i) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (fun _ : Fin 1 => th j) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => b i k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (b j) (fun k' => M.val k k') t) ∧
    (A.U i ⊓ A.U j).topIso.inv.hom (A.g i j).val = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) ∧
  ∀ (i : A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ (A.U i).toScheme,
    Set.range (jK W ≫ χ ≫ (A.U i).ι) ⊆ abLocus G →
    BasisAlong G L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (fun _ : Fin 1 => th i) ∧
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (b i)

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem hasFrames_of_ampFrames (F : AmpFrames G L N) : HasFrames G L N F.A F.n F.r F.s := by
  refine ⟨F.th, F.b, ?_, ?_⟩
  · intro i j
    exact F.trans i j
  · intro i W _ _ _ hW χ hχ
    exact F.trait i W hW χ hχ

theorem exists_ampFrames {A : LB Z} {n : ℕ} {r s : ℤ} (hA : A.IsLB) (ha : AmpleFam A) (h : HasFrames G L N A n r s) :
    ∃ F : AmpFrames G L N, F.A = A ∧ F.n = n ∧ F.r = r ∧ F.s = s := by

  obtain ⟨th, b, htr, htrait⟩ := h
  exact ⟨⟨A, hA, ha, n, th, b, r, s, htr, htrait⟩, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ModelSum

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaDescent

def gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) : Subfield K :=
  Subfield.closure (Set.range β ∪ s)

theorem gen_mono {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    gen β s ≤ gen β s' :=
  Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))

theorem subset_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ gen β s' :=
  fun _ hx => Subfield.subset_closure (Or.inr (h hx))

theorem mem_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) (a : o) : β a ∈ gen β s :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem countable_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) [Countable o] :
    Countable (gen β s) := by
  have hc : (Set.range β ∪ (s : Set K)).Countable := (Set.countable_range β).union s.countable_toSet
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem descends_of
    (hproj : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype))
    (hmor : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀)
    (hgrp : ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ)
    (hlb : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ))
    (hobj : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i)) :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  intro o _ g k J b _ K _ β t
  classical
  obtain ⟨s₀, H₀⟩ := hproj K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := hgrp K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := hlb K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := hmor K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ J (fun j => (t.act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := hmor K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * g)) (fun a => (t.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  let β₁ : o →+* gen β s := β.codRestrict _ (mem_gen β s)
  have hβ : (gen β s).subtype.comp β₁ = β := rfl
  obtain ⟨t₀, ht₀⟩ := hobj o g k J b (gen β s) K (gen β s).subtype β₁ β t A₁ ψ L₁ pt₁ act₁ hβ hG hL₁ hL
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
      have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁]
        exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, hψ₂, ← Category.assoc, e]
        refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        exact ((congrArg _ e₂).trans (Category.comp_id _)).symm)
    (fun j => by
      have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
      · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂])
  exact ⟨gen β s, β₁, t₀, hβ, fun _ => countable_gen β s, ⟨s, rfl⟩, ht₀⟩

theorem descends_to_fg_subfield :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) :=
  descends_of (@GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield) (@GlobalTheory.T.exists_descent_of_morphisms_to_subfield) (@GlobalTheory.grpObj_descends_to_large_subfield) (@GlobalTheory.T.exists_lineBundle_descent_to_subfield) (@GlobalTheory.exists_thetaObj_of_descended_data)

end GlobalTheory.ThetaDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS
private theorem k_ne_zero_lemma {o : Type} [CommRing o] {k : ℕ} (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) :
    k ≠ 0 := by
  rintro rfl
  have h0 : (0 : o) = 1 := isUnit_zero_iff.mp (by simpa using b.unit)
  haveI : Subsingleton o := subsingleton_of_zero_eq_one h0
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum ℂ))
  exact (s₀.base x).isPrime.ne_top (Subsingleton.elim _ _)

theorem tMap_of_isConst : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  intro hL hL2 hT o _ g k J b s₀ s' t₀ t' ρ j hc ⟨hpb, hlb, hpt, hact⟩
  have hk : k ≠ 0 := k_ne_zero_lemma b s₀
  refine ⟨ρ, hc.1, ?_, ?_, ?_⟩
  · obtain ⟨u, Hm, χ, hu, -⟩ := GlobalTheory.KSInh.exists_goodU_ksRel hT t₀.pol
    exact GlobalTheory.SymRigid.lbIso_pull_of_isConst hL t₀.pol u Hm χ hu t'.A ρ j hc t'.L t'.isLB t'.sym hlb
  · intro i
    exact GlobalTheory.T.torsionSection_constantFamily_dualNumbers hL t₀.pol t'.A ρ j hc k (t'.pt i) (t₀.pt i) hk (t'.torsion i) (t₀.torsion i) (hpt i).symm
  · intro jj
    exact GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange hL hL2 t₀.pol t'.A ρ j hc (t'.act jj) (t₀.act jj) t'.ab (t'.hom jj) (t₀.hom jj) (hact jj).symm
end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  first | exact @GlobalTheory.exists_locDer_top_of_ksRel_zero | exact GlobalTheory.exists_locDer_top_of_ksRel_zero | (intros; apply GlobalTheory.exists_locDer_top_of_ksRel_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_abelianTriple_descent_galoisCover : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (t : SAB H X) (g : ℕ) (ν : ∀ a, SABMap t t (ρ a)), IsGaloisCover Ga ρ π → IsQProjOver sY → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (ν 1).φ = 𝟙 _ → (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) → ∃ (t' : SAB H Y) (m : SABMap t t' π), (∀ a, (ν a).φ ≫ m.φ = m.φ) ∧ IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | exact GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | (intros; apply GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  first | exact @GlobalTheory.cubWeil_perfect_of_generic | exact GlobalTheory.cubWeil_perfect_of_generic | (intros; apply GlobalTheory.cubWeil_perfect_of_generic <;> assumption)
end
