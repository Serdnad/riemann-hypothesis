module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDualExponentialLeOfAinfValued
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle445
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WachTensor

noncomputable section

namespace GlobalTheory.NL.BaseField

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}

theorem res_eq_one_iff (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) : W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h1 := W.χΓ_res g
  rw [P.PD_χ] at h1
  constructor
  · intro h
    rw [h, map_one, Units.val_one, map_one] at h1
    exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (h1.symm.trans (map_one _).symm))
  · intro h
    rw [h, Units.val_one, map_one] at h1
    apply W.χΓ_inj
    rw [map_one]
    exact Units.ext (Subtype.ext h1)

theorem ker_transfer {K' : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K')))
    (h : Good K s LL) (h0 : K0 K = K0 K') (g' : ↥(GK K')) (hg : W'.resΓ g' = 1) :
    ∃ g : ↥(GK K), W.resΓ g = 1 ∧ (g : GQ l) = g' :=
  have h1 := (res_eq_one_iff W' g').1 hg
  ⟨⟨g', mem_GK_of_chi P h.2.2.1 h0 g'.2 h1⟩, (res_eq_one_iff W _).2 h1, rfl⟩

theorem sep_of_hausdorff {R : Type} [CommRing R] (a : R) (h : IsHausdorff (Ideal.span {a}) R) (x : R)
    (hx : ∀ k : ℕ, a ^ k ∣ x) : x = 0 :=
  h.haus x fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end Concrete



theorem rings_mem (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (h0 : K0 K = K0 K') :
    (∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a) ∧
      ∀ a, ∃ a', ((F l).E K' s LL h').tie.ioE a' = ((F l).E K s LL h).tie.ioE a := by
  obtain ⟨c1, -, c3, -, c5⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  have h1 : ∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a :=
    io_mem _ _ Subtype.val_injective (descends _) c3 (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.2.2.1
      (fun g' hg' => by
        obtain ⟨g, hg, e⟩ := ker_transfer _ _ h h0 g' hg'
        exact ⟨g, hg, congrArg ((D.locA l).gRW LL) e⟩)
      (sep_of_hausdorff _ (c5 _ (GlobalTheory.Cyc.εroot_sub_one_not_unit (D.locA l) s)).toIsHausdorff)
  refine ⟨h1, ioE_mem _ _ (((D.loc l).PD_p K').trans ((D.loc l).PD_p K).symm) h1 ?_⟩
  rw [(D.loc l).PD_p K]
  exact sep_of_hausdorff _ c1.toIsHausdorff

section Two

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K K' : FinExt l} {s : ℕ} {LL : FinExt l}
  {h : Good K s LL} {h' : Good K' s LL}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  {W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K'))}
  (E : EtSit P AI K s LL h W) (E' : EtSit P AI K' s LL h' W') (T : Lt K LL) (T' : Lt K' LL)



theorem jD_mem_sit (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T)
    (he : ∀ (g : ↥(GK K)) (g' : ↥(GK K')), (g : GQ l) = g' → ∀ t, e (T.actT g t) = T'.actT g' (e t))
    (x : W.DD T) : ∃ x', E'.tie.jD T' x' =
      TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) e (E.tie.jD T x) :=
  jD_mem E.tie E'.tie (descends E') (map_ne_top E) (φRW_surjective LL) hE T T' e (fun g' hg' =>
    (ker_transfer W W' h h0 g' hg').imp fun g hg => ⟨hg.1, congrArg (AI.gRW LL) hg.2, he g g' hg.2⟩) x

variable (hle : K.1 ≤ K'.1) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T)
  (hact : ∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t))

include hact in
theorem act_fwd (g' : ↥(GK K')) (g : ↥(GK K)) (e : (g' : GQ l) = g) (t : ↥T'.L.T) :
    eT.toLinearMap (T'.actT g' t) = T.actT g (eT.toLinearMap t) :=
  (hact g' t).trans (congrArg (fun u : ↥(GK K) => T.actT u (eT t)) (Subtype.ext e))

include hact in
theorem act_bwd (g : ↥(GK K)) (g' : ↥(GK K')) (e : (g : GQ l) = g') (t : ↥T.L.T) :
    eT.symm.toLinearMap (T.actT g t) = T'.actT g' (eT.symm.toLinearMap t) := by
  apply eT.injective
  have h1 := act_fwd T T' hle eT hact g' g e.symm (eT.symm t)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 ⊢
  exact h1.symm


include hact in
theorem jD_bwd (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x) (x : W.DD T) :
    ∃ x', TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap
      (E'.tie.jD T' x') = E.tie.jD T x :=
  (jD_mem_sit E E' T T' h0 hE eT.symm.toLinearMap (act_bwd T T' hle eT hact) x).imp fun _ hx' =>
    (congrArg (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) hx').trans
      (map_id_symm eT.symm (E.tie.jD T x))


include hact in
theorem modules_eq (h0 : K0 K' = K0 K) (a1 : ∀ x, ∃ x', E'.tie.io x' = E.tie.io x)
    (a2 : ∀ x, ∃ x', E.tie.io x' = E'.tie.io x) (e1 : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e2 : ∀ x, ∃ x', E.tie.ioE x' = E'.tie.ioE x) (hQ : E'.tie.io W'.Q = E.tie.io W.Q)
    (hinj : Function.Injective E'.tie.ioE)
    (hb : IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)))
    (h10 : IsCrys (P.PD K') T'.ρ → p10 W' T') :
    (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.tie.jD T') =
      Set.range (E.tie.jD T) ∧ (IsCrys (P.PD K) T.ρ → IsCrys (P.PD K') T'.ρ →
      (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) ''
        (E'.tie.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.tie.jD T '' (W.N T : Set (W.DD T))) := by
  have d1 := jD_mem_sit E' E T' T h0 e2 eT.toLinearMap (act_fwd T T' hle eT hact)
  have d2 := jD_bwd E E' T T' hle eT hact h0.symm e1
  refine ⟨Set.Subset.antisymm ?_ ?_, fun hT hT' => ?_⟩
  · rintro _ ⟨_, ⟨x', rfl⟩, rfl⟩
    exact d1 x'
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := d2 x
    exact ⟨_, ⟨x', rfl⟩, hx'⟩
  · exact (hb hT).elim fun b => N_eq E.tie E'.tie T T' eT hT (h10 hT') b hinj a1 a2 e1 hQ d2 d1
      fun g' => ⟨⟨(g' : GQ l), GK_le hle g'.2⟩, rfl, hact g'⟩

end Two



theorem base_indep : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → let W' := (HW l).W K' s LL h'; let E' := ((F l).E K' s LL h').tie; Set.range E.io = Set.range E'.io ∧ Set.range E.ioE = Set.range E'.ioE ∧ ∀ (T : Lt K LL) (T' : Lt K' LL) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T), (∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t)) → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.jD T') = Set.range (E.jD T) ∧ (IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K') T'.ρ → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' (E'.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.jD T '' (W.N T : Set (W.DD T))) := by
  intro D HW F l _ K s LL h W E K' h' hle h0 W' E'
  have a1 := (rings_mem D HW F l K s LL h K' h' h0.symm).1
  have e1 := (rings_mem D HW F l K s LL h K' h' h0.symm).2
  have a2 := (rings_mem D HW F l K' s LL h' K h h0).1
  have e2 := (rings_mem D HW F l K' s LL h' K h h0).2
  have q := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have q1 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.1
  have q2 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.1
  refine ⟨?_, ?_, fun T T' eT hact => ?_⟩
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 a1) (Set.range_subset_iff.2 a2)
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 e1) (Set.range_subset_iff.2 e2)
  have hb := N_basis D HW F l K s LL h T
  have h10 : IsCrys ((D.loc l).PD K') T'.ρ → p10 ((HW l).W K' s LL h') T' := GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K' s LL h' T'
  exact modules_eq ((F l).E K s LL h) ((F l).E K' s LL h') T T' hle eT hact h0 a1 a2 e1 e2 (q1.trans q.symm)
    q2 hb h10

end GlobalTheory.NL.BaseField
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.mem_wach_of_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.CocycleInj.main | exact GlobalTheory.NL.CocycleInj.main | (intros; apply GlobalTheory.NL.CocycleInj.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem exists_extend_residue {O A F : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Algebra.IsIntegral O A] (hinj : Function.Injective (algebraMap O A)) [Field F] [IsAlgClosed F]
    (κ : IsLocalRing.ResidueField O →+* F) :
    ∃ g : A →+* F, g.comp (algebraMap O A) = κ.comp (IsLocalRing.residue O) := by
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (IsLocalRing.maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (A ⧸ Q) := Ideal.Quotient.field Q
  let j : IsLocalRing.ResidueField O →+* A ⧸ Q := Ideal.quotientMap Q (algebraMap O A) hQm.ge
  have hj : j.comp (IsLocalRing.residue O) = (Ideal.Quotient.mk Q).comp (algebraMap O A) := by
    ext x; rfl
  letI : Algebra (IsLocalRing.ResidueField O) (A ⧸ Q) := j.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) F := κ.toAlgebra
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
    refine ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (j.comp (IsLocalRing.residue O)) _ _ = 0
    rw [hj, ← hom_eval₂, hpa, map_zero]⟩
  let L : (A ⧸ Q) →ₐ[IsLocalRing.ResidueField O] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  rw [RingHom.comp_assoc, ← hj, ← RingHom.comp_assoc]
  congr 1
  ext x
  exact L.commutes x

theorem exists_redVia : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
      InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  intro D i k _
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hφ : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  letI : Algebra (D.nd.O i) ℂ := (iotaO D.nd D.naut i).toAlgebra
  let A := integralClosure (D.nd.O i) ℂ
  have hA : Function.Injective (algebraMap (D.nd.O i) A) := fun x y h => hφ (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_extend_residue hA (D.naut.kFbar i)
  have hmem : ∀ x, D.ntypes.teichC k x ∈ A := by
    intro x
    by_cases hx : x = 0
    · rw [hx, GlobalTheory.TameLabels.teich_zero _ (D.ntypes.teichC_inj k)]; exact A.zero_mem
    · obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1
        ((D.ntypes.teichC k).isOfFinOrder (GlobalTheory.TameLabels.isOfFinOrder_of_ne_zero hx))
      exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  let t : Fb (D.host.g k) (D.host.g_prime k) →* A := (D.ntypes.teichC k).codRestrict A.toSubmonoid hmem
  have ht : ∀ x, (t x : ℂ) = D.ntypes.teichC k x := fun _ => rfl
  refine ⟨g.toMonoidHom.comp t, fun x y hx hy hcx hcy h => ?_, fun p s hp => ?_⟩
  · refine D.ntypes.teichC_inj k x y hx hy ?_
    rw [← ht, ← ht]
    congr 1
    refine GlobalTheory.TameRed.eq_of_map_eq g (M := orderOf x * orderOf y) ?_ ?_ ?_ h
    · rw [Ne, CharP.cast_eq_zero_iff _ (D.nd.l i)]
      exact (Nat.Prime.coprime_iff_not_dvd (D.nd.lPrime i).out).1 (Nat.Coprime.mul_left hcx hcy).symm
    · rw [← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
    · rw [← map_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
  · have h1 : p.map (algebraMap (D.nd.O i) A) = (s.map fun x => X - C (t x)).prod := by
      apply Polynomial.map_injective A.val.toRingHom Subtype.val_injective
      rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
      refine hp.trans (congrArg _ (Multiset.map_congr rfl fun x _ => ?_))
      simp [ht]
    rw [← hg, ← Polynomial.map_map, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
    simp

end GlobalTheory.TypeLeaf
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.norm_dualExponential_le_of_ainf_valued : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ (z : GQ l → ℚ_[l]) (α : Om l), α ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → (∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR (z σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) → ‖α‖ ≤ (l : ℝ) ^ (((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) + (e : ℝ) / ((l : ℝ) - 1)) := by
  first | exact @GlobalTheory.Cyc.ExpBound.norm_expStar_le | exact GlobalTheory.Cyc.ExpBound.norm_expStar_le | (intros; apply GlobalTheory.Cyc.ExpBound.norm_expStar_le <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.CuspMultisetCount

theorem degL_toList {g : ℕ} [Fact g.Prime] (M : Multiset (Pc g)) :
    degL M.toList = (M.map fun p => p.1).sum := by
  unfold degL
  conv_rhs => rw [← Multiset.coe_toList M]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem stdAddChar_ne_one (g : ℕ) [Fact g.Prime] : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) ≠ 1 := by
  intro h
  have h1 := congrArg (fun ψ : AddChar (ZMod g) ℂ => ψ 1) h
  simp only [AddChar.one_apply] at h1
  have h0 : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) 0 = 1 := AddChar.map_zero_eq_one _
  have := ZMod.injective_stdAddChar (N := g) (h1.trans h0.symm)
  exact one_ne_zero this

theorem card_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)),
    (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  intro g _ n hn S hS
  set ψ : AddChar (ZMod g) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ ≠ 1 := stdAddChar_ne_one g
  have hdeg : ∀ M ∈ S, degL M.toList = n := fun M hM => (degL_toList M).trans (hS M hM).1
  have hcusp : ∀ M ∈ S, ∀ p ∈ M.toList, IsCusp p.2 := fun M hM p hp =>
    (hS M hM).2 p (Multiset.mem_toList.1 hp)
  have hchar : ∀ M ∈ S, IsChar (hcL M.toList n) := fun M hM =>
    (GlobalTheory.gl_list_product_perm_char g M.toList M.toList n (hdeg M hM).symm
      (fun p hp => Label.isChar_of_isIrr (hcusp M hM p hp).2.1)).1
  have key : ∀ M ∈ S, ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL M.toList n) ≠ 0 :=
    fun M hM => GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal g ψ hψ M.toList n (hdeg M hM) (hcusp M hM)
  choose! f hf using key
  have hfin : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.Finite :=
    (GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one (Gn g n)).1.subset fun ρ h => h.1
  have hinj : Set.InjOn f (S : Set (Multiset (Pc g))) := by
    intro M hM M' hM' heq
    have h1 := (hf M hM).2.2
    have h2 := (hf M' hM').2.2
    rw [heq] at h1
    have hne := Label.ip_ne_zero_of_common (f M') _ _ (hf M' hM').1 (hchar M hM) (hchar M' hM') h1 h2
    have hp : M.toList.Perm M'.toList := by
      by_contra hnp
      exact hne ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g M.toList M'.toList n (hdeg M hM) (hdeg M' hM')
        (hcusp M hM) (hcusp M' hM')).1 hnp)
    rw [← Multiset.coe_toList M, ← Multiset.coe_toList M']
    exact Multiset.coe_eq_coe.2 hp
  calc S.card = (S : Set (Multiset (Pc g))).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.ncard :=
        Set.ncard_le_ncard_of_injOn f (fun M hM => ⟨(hf M hM).1, (hf M hM).2.1⟩) hinj hfin
    _ ≤ g ^ n - g ^ (n - 1) := GlobalTheory.T.ncard_generic_irreducible_characters_GLn_le g ψ hψ n hn

end GlobalTheory.GLq.CuspMultisetCount
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  first | exact @GlobalTheory.GLq.DetSplit.root_of_constituent | exact GlobalTheory.GLq.DetSplit.root_of_constituent | (intros; apply GlobalTheory.GLq.DetSplit.root_of_constituent <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.TateDualInv.noInv_tateDual | exact GlobalTheory.TateDualInv.noInv_tateDual | (intros; apply GlobalTheory.TateDualInv.noInv_tateDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RatSpanProof

theorem ratSpan_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t
  exact GlobalTheory.HeckeClassSums.span_jV hL.models.HV hL.models.jV i t

end GlobalTheory.RatSpanProof
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowsCD

theorem lt_ratIn {x y : ℝ} (h : x < y) : x < ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_left h]
  exact (exists_rat_btwn h).choose_spec.1

theorem flat_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 < Formalism.MainNotions.N.flat L bd l := by
  unfold Formalism.MainNotions.N.flat
  have hE : 0 < Formalism.MainNotions.TwistedPlaces.eta₃ L := by
    unfold Formalism.MainNotions.TwistedPlaces.eta₃; have := L.etaSz_pos; positivity
  have hW : 0 ≤ Formalism.MainNotions.TwistedPlaces.wP L := by
    unfold Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.wB
    have h1 := Formalism.MainNotions.TwistedPlaces.w''_nonneg L
    have h2 := L.etaSz_pos
    have h3 := le_max_left (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)
    have h4 : (0 : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by positivity
    linarith
  have h1 : 0 ≤ (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / (l : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h3 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have h4 := L.Sc_pos
  by_cases hb : bd
  · rw [if_pos hb]; linarith
  · rw [if_neg hb]; linarith

theorem coreF_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreF L bd l lam := by
  unfold Formalism.MainNotions.N.coreF
  have hr : (0 : ℝ) < D.R.r := by linarith [Formalism.MainNotions.TwistedPlaces.k_le_r D, Formalism.MainNotions.TwistedPlaces.k_ge_five D]
  have hn : (0 : ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  exact mul_pos (mul_pos hn hr) (flat_pos L bd l)

theorem bdCD_lt {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E))
    (K₁ K₂ K₃ : ℝ) : Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ < Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ := by
  have e : Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ =
      Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ + Formalism.MainNotions.N.coreF L bd l lam := by
    unfold Formalism.MainNotions.N.bdCD; ring
  rw [e]
  linarith [coreF_pos L bd l lam]

end GlobalTheory.NLink.RowsCD

theorem GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  intro D L P HW F C₂ i r ρ π dc h17 h04 h54 h67 hl hπ hJ w hw _ C hC
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨hur, hW⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hB, hBox, hcase⟩ := hW C hg
  have hrow : RowL i r ρ π w hw C (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w
      (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
    rcases hcase with hNT | ⟨hC', d, hAT⟩
    · exact GlobalTheory.T.rowBounds_of_nonThick_letter D L P HW F C₂ i r ρ π w hw C hg Wd h17 h54 h67 hl hπ hB hBox hNT
    · exact GlobalTheory.T.rowBounds_of_all_letters_thick D L P HW F C₂ i r ρ π w hw C hg Wd d _ h04 h54 h67 hl hB hBox hC' hAT
  exact GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow
    (GlobalTheory.NLink.RowsCD.lt_ratIn (GlobalTheory.NLink.RowsCD.bdCD_lt L _ _ w _ _ _)).le
end
