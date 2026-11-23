module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle952
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaar
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039

@[expose] public section

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachFrame

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) {T : LocLat G Qp LL O} {n : ℕ}

theorem γD_smulA (g : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem coe_eq_sum (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (y : ↥(W.N T)) :
    (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := by
  have h1 := congrArg Subtype.val (b.sum_repr y)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
  exact h1.symm

theorem coord_fixed (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) (hy : W.γD T δ (y : W.DD T) = y) (m : Fin n) :
    W.γA δ (b.repr y m) = b.repr y m := by
  have e : ∑ m, W.γA δ (b.repr y m) • b m = y := by
    apply Subtype.ext
    have h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T) := by

      conv_lhs => rw [coe_eq_sum W b y, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [γD_smulA, (hb m).2 δ hδ]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact h1.symm.trans hy
  have h2 := congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m
  rw [e] at h2
  exact h2.symm

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_inc (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) (m : Fin n) (i : ZMod f) :
    ∃ z, inc l O z = b.repr y m i :=
  hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i

theorem exists_phi_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hφ : ∀ x ∈ W.N T, W.φD T x ∈ W.N T) :
    ∃ Pm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.φD T (b k : W.DD T) =
      ∑ m, (fun i => inc l O (Pm i m k) : LetA O f) • (b m : W.DD T) := by
  have h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i := fun i m k =>
    exists_inc W l hI b hb _ (fun δ hδ => by
      change W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)
      rw [← W.φγ_comm, (hb k).2 δ hδ]) m i
  choose Pm hPm using h
  refine ⟨fun i => Matrix.of (Pm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hPm i m k).symm

theorem exists_gam_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (γ : W.Gam) :
    ∃ Dm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • Dm i) m k) : LetA O f) • (b m : W.DD T) := by
  have hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T := fun k => W.N_Γ T γ _ (b k).2
  have h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) =
      b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i := by
    intro i m k
    obtain ⟨z, hz⟩ := exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by
      change W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i
    obtain ⟨y, hy, e⟩ := W.N_π T γ _ (b k).2
    have e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T)) :=
      Subtype.ext (eq_add_of_sub_eq' e)
    have e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0 := by
      rw [map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add (f := _), map_smul, b.repr_self]
      by_cases hmk : m = k
      · subst hmk
        simp [letπ]
      · simp [letπ, hmk, Finsupp.single_eq_of_ne hmk]
    obtain ⟨d, hd⟩ := X_dvd_iff.2 e2
    exact ⟨d, by rw [← hd, add_sub_cancel, hz]⟩
  choose Dm hDm using h
  refine ⟨fun i => Matrix.of (Dm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hDm i m k).symm

theorem mem_of_letters (x : W.DD T) (h : ∀ i, (letE i : LetA O f) • x ∈ W.N T) : x ∈ W.N T := by
  haveI := GlobalTheory.WachLettersCompare.neZero_letters W
  have e : (∑ i, letE i : LetA O f) = 1 := Finset.univ_sum_single (1 : LetA O f)
  rw [← one_smul (LetA O f) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => h i

theorem phi_mem (hH : GlobalTheory.WachUse.Heights W) (U : ZMod f → Multiset ℤ)
    (hU : GlobalTheory.AdmLoc.CrysWith PD W.emb T.ρ U) (hpos : ∀ i, ∀ u ∈ U i, 0 ≤ u) :
    ∀ x ∈ W.N T, W.φD T x ∈ W.N T := by
  intro x hx
  refine mem_of_letters W _ fun i => ?_
  have := (hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx
  · simpa using this
  · refine ⟨by simpa using hpos i u hu, ?_⟩
    have h1 : u.toNat ≤ ((U i).map Int.toNat).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)
    exact (Int.self_le_toNat u).trans (by exact_mod_cast h1)

end Generic

theorem exists_rem {l : ℕ} [Fact l.Prime] (LL : FinExt l) (g : (↥(OL LL))⟦X⟧) :
    ∃ a : ↥(OL LL), (X - C (l : ↥(OL LL))) ∣ g - C a := by
  obtain ⟨_, hc, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨g₁, a, e⟩ := (linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL))
    ((mem_maximalIdeal _).2 hl)).1 g
  exact ⟨a, g₁, by rw [e, add_sub_cancel_right]⟩

theorem exists_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  intro D HW F Cm l _ K LL hA T U n hU hpos hn γ
  have hR := GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA
  have hJ := (GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2
    ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩
  have hH := GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩
    ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩
  obtain ⟨Pm, hP⟩ := exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)
  obtain ⟨Dm, hD⟩ := exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ
  choose Th hTh using fun i a c => exists_rem LL (Dm i a c)
  exact ⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩

end GlobalTheory.WachFrame

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ 2 * lam s := by
  first | exact @GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | exact GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | (intros; apply GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam <;> assumption)
end

section

set_option autoImplicit false


noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A]
  {π : A.left ⟶ Xo.univ.t.G.left}

theorem one_comp (hπ : IsGrpPullback A Xo.univ.t.G x π) :
    η[A].left ≫ π = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ (Over (Sp K)))))
  have e₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [GlobalTheory.ArcQ.NormalForm.one_left_eq, GlobalTheory.ArcQ.NormalForm.one_left_eq]
  simp

theorem exists_lift (hπ : IsGrpPullback A Xo.univ.t.G x π) {T : Over (Sp K)} (v : T.left ⟶ Xo.univ.t.G.left)
    (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) : ∃ w : T ⟶ A, w.left ≫ π = v :=
  ⟨Over.homMk (hπ.1.lift v T.hom hv) (hπ.1.lift_snd _ _ _), hπ.1.lift_fst _ _ _⟩

theorem tan_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR K ⟶ A) : IsTanAt x (w.left ≫ π) ↔ IsTangent w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  constructor
  · intro h
    apply hπ.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_comp hπ).symm
    · have a : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hw, a, ← Geo.Tor.spMap_comp]
      have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, hπ.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) h).trans (one_comp hπ)

theorem eig_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) {f : A ⟶ A} {g : Xo.univ.t.G ⟶ Xo.univ.t.G}
    (hf : f.left ≫ π = π ≫ g.left) (w : epsR K ⟶ A) (s : K) :
    (w.left ≫ π) ≫ g.left = spMap (epsMul s) ≫ w.left ≫ π ↔
      w ≫ f = GlobalTheory.GrpTangent.epsScale s ≫ w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  have e : (w.left ≫ π) ≫ g.left = (w ≫ f).left ≫ π := by
    rw [Over.comp_left, Category.assoc, Category.assoc, hf]
  rw [e]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · simp only [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc] at h ⊢
      exact h
    · rw [Over.w, Over.w]
  · intro h
    rw [h, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc]
    rfl

theorem push_prod (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) :
    ((List.ofFn u).prod).left ≫ π = ((List.ofFn fun i => pushHom hπ (epsR K) (u i)).prod).left := by
  have := map_list_prod (pushHom hπ (epsR K)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem isLieComb_of_isCombAt (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR K ⟶ A))
    (cf : Fin n → K) (w : epsR K ⟶ A)
    (h : IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π)) : IsLieComb cf v w := by
  obtain ⟨u, hu, hw⟩ := h
  choose u' hu' using fun i => exists_lift hπ (T := epsR K) (u i).left (Over.w (u i))
  have e : u = fun i => pushHom hπ (epsR K) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
  refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
  · apply hπ.1.hom_ext
    · rw [Category.assoc]; exact (hu' i).trans (hu i)
    · have hv : (v i).left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w (v i)
      rw [Over.w, Category.assoc, hv, ArcQ.NormalForm.ExFr.scale_over]; rfl
  · apply hπ.1.hom_ext
    · rw [e] at hw
      exact hw.symm.trans (push_prod hπ u').symm
    · rw [Over.w, Over.w]

end GlobalTheory.KSExist.FrameLift

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left} (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR K ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR K) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

open GlobalTheory.DefU.ClassFin

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tw (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

theorem tw_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tw n c g)⁻¹).val = cT c g.val := rfl

theorem tw_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tw n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem map_tw (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tw n c g) = tw n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pU : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU (E := E) (n := n)).subtype

theorem finGL_pU (k : finU (E := E) (n := n)) : finGL E n (pU k) = k.1.1 := finGL_pFin k

theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

theorem tw_pU (k : finU (E := E) (n := n)) : tw n (conjFin (cc E)) (pU k) = pU k := (tw_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : finU (E := E) (n := n) :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tw_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

theorem pU_sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

theorem ratF_tw (g : GL (Fin n) E) :
    ratF E n (tw n (cc E).toRingHom g) = tw n (conjFin (cc E)) (ratF E n g) :=
  map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tw n (cc E).toRingHom g = g := by
  rw [tw_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tw, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

theorem mem_ratFinU (k : finU (E := E) (n := n)) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tw, hg, tw_pU]

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  intro E _ _ _ n
  refine ⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩
  · rw [map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]
  · rw [← pU_finPt, ← pU_finPt, h]
  · rw [mem_ratFinU]
    constructor
    · rintro ⟨g, hg⟩
      have hU : g ∈ UE E n := (mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))
      exact ⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, (pU_finPt γ).symm⟩

end GlobalTheory.BCT.FinPart
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n), IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) → (∀ v ∈ U, v ∉ K → f j v = 0) → ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | exact GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | (intros; apply GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first | exact @GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine | exact GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine | (intros; apply GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  first | exact @GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField | exact GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField | (intros; apply GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField <;> assumption)
end
