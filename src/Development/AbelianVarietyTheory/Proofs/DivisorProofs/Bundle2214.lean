module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieFrame

theorem one_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushPt h.1.w (1 : T ⟶ G') = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  refine (congrArg Over.Hom.left e').trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact Category.assoc _ _ _

theorem exists_hom {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ') :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  refine ⟨F, hF, ?_⟩
  rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]

theorem dual_w {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pull {V O : Type} [CommRing V] [CommRing O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
    {f : V →+* O} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) π) {u : epsOver V V ⟶ G} (hu : IsTan u) :
    ∃ x : LieG G', x.1.left ≫ π = spMap (dualMap f) ≫ u.left := by
  have w : (spMap (dualMap f) ≫ u.left) ≫ G.hom = spMap (algebraMap O (DualNumber O)) ≫ spMap f := by
    rw [Category.assoc, Over.w u, ← dual_w]
    rfl
  refine ⟨⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_⟩, h.1.lift_fst _ _ w⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine Eq.trans ?_ (one_comp h (specO O O)).symm
  change (spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ h.1.lift _ _ w) ≫ π = spMap (algebraMap O O) ≫ _
  have e : spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (dualMap f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
    rw [spMap_spMap, spMap_spMap]
    congr 1
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, h.1.lift_fst, ← Category.assoc, e, Category.assoc, hu, Hom.one_def, Over.comp_left,
    Over.toUnit_left]
  change spMap f ≫ spMap (algebraMap V V) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]

theorem exists_lieTie_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∃ x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt, ∀ τ j, LieTie P ψ (x τ j) (z.u τ j) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz
  letI := io.toAlgebra
  obtain ⟨hk, G, t', m₁, m₂, π, φ, hπ, -, hφ, h4, rfl, -⟩ := hP
  obtain ⟨G₀, t₀, n₁, n₂, ⟨ub, ht, -, -, hub⟩, -⟩ := y₀.2.2
  obtain ⟨e, he, h₁⟩ := grpPullback_iso n₁.cart m₁.cart
  have h₂ : IsGrpPullback t₀.G G.G (spMap (algebraMap T.V T.Fr)) (e.hom.left ≫ m₂.φ) :=
    ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl
  obtain ⟨F, hF, h₃⟩ := exists_hom G₀.semi G.semi n₂.cart h₂
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  suffices h : ∀ τ j, ∃ x : LieG P.Gt, LieTie P (φ ≫ m₁.φ) x (z.u τ j) by
    choose x hx using h
    exact ⟨x, hx⟩
  intro τ j
  obtain ⟨u', h5, h6⟩ := hub τ j
  have ht' : IsTan (ub τ j ≫ F) := by
    unfold IsTan
    rw [Over.comp_left, ← Category.assoc, ht τ j, ← Over.comp_left, MonObj.one_comp]
  obtain ⟨xG, hx⟩ := exists_pull hπ ht'
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hadic : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h : IsAdicComplete (Ideal.span {(p : O)}) O := inferInstance
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  obtain ⟨x, hc, -⟩ := existsUnique_left (P := P) hp hadic xG.1
  have h7 := hc.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h7
  have hu : (u' ≫ e.hom.left) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    haveI : Mono (spMap (algebraMap T.V T.Fr)) :=
      haveI : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
      inferInstance
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, Category.assoc, ← m₂.cart.1.w,
      ← Category.assoc e.hom.left, ← h₃, Category.assoc, Over.w F, ← Category.assoc, h6, Category.assoc,
      Over.w (ub τ j), ← dual_w]
    rfl
  have w : (spMap (dualMap k.toRingHom) ≫ u' ≫ e.hom.left) ≫ t'.G.hom =
      spMap (algebraMap C (DualNumber C)) ≫ spMap k.toRingHom := by
    rw [Category.assoc, hu, dual_w]
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique h7 Corr.one⟩, xG,
    Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w), hc, ?_, hπ.1.hom_ext ?_ ?_⟩
  · change hφ.1.lift _ _ w ≫ _ = _
    rw [hφ.1.lift_fst_assoc, hz.2.1, ← h5, Category.assoc, Category.assoc, h₁]
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, ← h4, hφ.1.lift_fst_assoc, Category.assoc, Category.assoc, ← h₃, ← Category.assoc u', h6,
      Category.assoc, Category.assoc, hx, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap,
      spMap_spMap, Over.comp_left]
    congr 2
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_
    · simpa [dualMap] using (hk s.fst).symm
    · simpa [dualMap, Algebra.algebraMap_eq_smul_one] using (hk s.snd).symm
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, P.gen_pull.1.w, hφ.1.lift_snd_assoc, Category.assoc, Over.w xG.1]
    exact (dual_w _).symm

end GlobalTheory.CompHt.TieFrame
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieIndep

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}

theorem lieTie_add {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp C ⟶ S} {ψ : P.A.A.left ⟶ G.left}
    (hψ : IsGrpPullback P.A.A G y ψ) {x x' : LieG P.Gt}
    {u u' : Over.mk (spMap (algebraMap C (DualNumber C)) ≫ y) ⟶ G}
    (h : LieTie P ψ x u.left) (h' : LieTie P ψ x' u'.left) : LieTie P ψ (lieAdd x x') (u * u').left := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  refine ⟨lieAdd xG xG', w * w', h1.mul h1', (hψ.2 _ w w' u u' h2.symm h2'.symm).symm, ?_⟩
  let d : Over.mk ((specO C (DualNumber C)).hom ≫ spMap (algebraMap O C)) ⟶ specO O (DualNumber O) :=
    Over.homMk (spMap (dualMap (algebraMap O C))) (by
      refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
      ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  refine (P.gen_pull.2 _ w w' (d ≫ xG.1) (d ≫ xG'.1) h3.symm h3'.symm).symm.trans ?_
  rw [← MonObj.comp_mul]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem lieTie_unique_right {Y : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {x : LieG P.Gt} {u u' : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P ψ x u') : u = u' := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => (Fact.out : ¬ IsUnit (p : O)) (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hc : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h := (inferInstance : IsAdicComplete (Ideal.span {(p : O)}) O)
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  have e : xG.1 = xG'.1 := (existsUnique_right hp hc x.1).unique h1 h1'
  have e1 : w.left = w'.left :=
    P.gen_pull.1.hom_ext (by rw [h3, h3', e]) ((Over.w w).trans (Over.w w').symm)
  rw [← h2, ← h2', e1]


omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem linearIndependent_evLie {n : ℕ} (x : Fin n → LieG P.Gt)
    (h : ∀ a : Fin n → O, (∀ f : omega P.Gt, ∑ j, a j * f.1 (x j) = 0) → ∀ j, a j = 0) :
    LinearIndependent C (fun j => evLie P (x j)) := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) g
  choose a ha using hb
  have h0 := h a (fun f => P.integers.hom_inj (by
    have h1 := congrArg (fun L : P.OmC →ₗ[C] C => (b : O) • L ((1 : C) ⊗ₜ f)) hg
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_zero, Finset.smul_sum] at h1

    rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ha, ← smul_assoc, smul_eq_mul]
    congr 1
    simp [evLie])) j
  have h2 := ha j
  rw [h0, map_zero, Algebra.smul_def] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left
    ((map_ne_zero_iff _ P.integers.hom_inj).2 (nonZeroDivisors.ne_zero b.2))

end GlobalTheory.CompHt.TieIndep

namespace GlobalTheory.CompHt


open TieIndep in
theorem linearIndependent_evLie_of_lieTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → LinearIndependent C (fun j => evLie P (x j)) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  have hψ : IsGrpPullback P.A.A Xo.univ.t.G z.x ψ := hz.1 ▸ hP.isGrpPullback
  obtain ⟨N, _, _, w, ρ, -, htan, hcomb, hρ, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo C z.x
  choose b hb using fun j => (htan _).1 (z.tan τ j)
  have hadd : ∀ {y y' : LieG P.Gt} {m m' : N}, LieTie P ψ y (w m) → LieTie P ψ y' (w m') →
      LieTie P ψ (lieAdd y y') (w (m + m')) := fun {y y' m m'} h h' => by
    obtain ⟨u, h1, h2⟩ := (hcomb 2 ![m, m'] ![1, 1] (w (m + m'))).2 (by simp)
    have e0 : (u 0).left = w m := (h1 0).trans ((hsm 1 m).symm.trans (by rw [one_smul]))
    have e1 : (u 1).left = w m' := (h1 1).trans ((hsm 1 m').symm.trans (by rw [one_smul]))
    rw [← h2, show (List.ofFn u).prod = u 0 * u 1 by simp]
    exact lieTie_add hψ (e0 ▸ h) (e1 ▸ h')
  have hsc : ∀ (a : O) j, LieTie P ψ (AvDefs.lieScale P.Gt a (x j)) (w (algebraMap O C a • b j)) := fun a j => by
    rw [hsm, hb]
    exact (hx j).scale a
  refine linearIndependent_evLie x fun a ha j => ?_
  have h0 := hsc 0 j
  rw [map_zero, zero_smul] at h0
  have hs : ∀ s : Finset (Fin (Dw.mult τ)), ∃ y, LieTie P ψ y (w (∑ i ∈ s, algebraMap O C (a i) • b i)) ∧
      ∀ f : omega P.Gt, f.1 y = ∑ i ∈ s, a i * f.1 (x i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨_, h0, fun f => by rw [omega_lieScale, zero_mul, Finset.sum_empty]⟩
    | insert i s hi ih =>
      obtain ⟨y, h1, h2⟩ := ih
      rw [Finset.sum_insert hi]
      exact ⟨_, hadd (hsc (a i) i) h1, fun f => by rw [omega_lieAdd, omega_lieScale, h2, Finset.sum_insert hi]⟩
  obtain ⟨y, h1, h2⟩ := hs Finset.univ
  have e : y = AvDefs.lieScale P.Gt 0 (x j) :=
    (Point.omega_free_finite_bijective p C v O (𝓞 E) P).2.2.1 (LinearMap.ext fun f => by
      change f.1 y = f.1 _
      rw [h2, ha, omega_lieScale, zero_mul])
  have e2 := lieTie_unique_right h0 (e ▸ h1)
  have hu : z.u τ = fun i => w (b i) := funext fun i => (hb i).symm
  have e3 := (z.basis τ (w 0) ((htan _).2 ⟨0, rfl⟩) fun t => by rw [← hρ, ← hsm, map_zero, smul_zero]).unique
    (y₁ := fun i => algebraMap O C (a i)) (y₂ := 0) (by rw [hu, hcomb]; exact e2) (by rw [hu, hcomb]; simp)
  exact P.integers.hom_inj ((congrFun e3 j).trans (map_zero _).symm)

end GlobalTheory.CompHt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

theorem vacuum_real_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  classical
  intro D T L sc G W U N σ h t j hj f hf
  by_contra hcon
  push_neg at hcon
  have hψ := hf.1
  have hS : IsSelfDualC (G.pS (.top t j)) (N.latS (.top t j)) :=
    N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hT : IsSelfDualC (G.pT (.top t j)) (N.latT (.top t j)) :=
    N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ _ _ hψ hS hT
  have hinf := fun u => GlobalTheory.VacUnique.latO_inf (u := u) (G.pS (.top t j)) (G.pT (.top t j))
    ((N.latS (.top t j) : Set _)) ((N.latT (.top t j) : Set _)) fun _ => True
  choose ε _ hε2 using h3 f hf.2.lat
  have e : f = 0 := by
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp h h2 w
    rw [hf.2.theta.quasi, GlobalTheory.VacUnique.apply_real_add h hψ (hinf u hu) (hε2 u hu f hf.2.lat), hcon z]
    simp
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 := hn p hp
  rw [e] at n1
  simp [nrm2] at n1

end GlobalTheory.VacRealForm

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  first | exact @GlobalTheory.tate_map_coker_card | exact GlobalTheory.tate_map_coker_card | (intros; apply GlobalTheory.tate_map_coker_card <;> assumption)
end
