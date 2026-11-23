module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle085
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle094
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FinOrder

variable {L : Type} [Field L] [NumberField L]

theorem exists_pow_congr (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (v.adicCompletion L)ˣ, _root_.Formalism.L2.Host.IsUnitAt v x →
      Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hu : Valued.v ((_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    _root_.Formalism.L2.Host.unif_spec v
  have hc : Valued.v (((_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hu, ← WithZero.exp_nsmul]; simp
  have hc1 : ((_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let c : v.adicCompletionIntegers L := ⟨_, hc1⟩
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n (Units.ne_zero _) (congrArg Subtype.val h)
  have : Finite (v.adicCompletionIntegers L ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  refine ⟨Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have hx : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hx' : Valued.v ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  let y : (v.adicCompletionIntegers L)ˣ :=
    ⟨⟨x, hx.le⟩, ⟨(x⁻¹ : (v.adicCompletion L)ˣ), hx'.le⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  have h1 := pow_card_eq_one' (x := Units.map (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom y)
  have h2 : Ideal.Quotient.mk (Ideal.span {c})
      ((y : v.adicCompletionIntegers L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ) =
      Ideal.Quotient.mk (Ideal.span {c}) 1 := by
    rw [map_pow, map_one]
    exact congrArg Units.val h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  have h3 : (a : v.adicCompletion L) * ((_root_.Formalism.L2.Host.atFin v (_root_.Formalism.L2.Host.unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n =
      (x : v.adicCompletion L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ - 1 :=
    congrArg Subtype.val ha
  rw [Units.val_pow_eq_pow_val, ← h3, map_mul, hc]
  exact mul_le_of_le_one_left' a.2

theorem triv_inf (χ : _root_.Formalism.L2.Host.HChar L) (h : ∀ k, χ.inf k = 1) (u : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    χ.1 (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) = 1 := by
  have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => χ.1 (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w))) = fun _ => 1 := by
    refine (GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer ?_ continuous_const ?_
    · exact χ.2.1.comp (continuous_finsetProd _ fun w _ =>
        (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))
    · funext k
      have h1 : χ.1 (_root_.Formalism.L2.Host.infDiag k) = 1 := h k
      unfold _root_.Formalism.L2.Host.infDiag at h1
      rw [MonoidHom.finsetProd_apply] at h1
      exact h1
  exact congrFun key u

theorem exists_decomp (a : _root_.Neutral.B1.Ideles L) :
    ∃ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, a = (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) * finPartI L a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    (Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp
      (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  let q : AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L :=
    MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  refine ⟨fun w => Units.map (p w) a, Units.ext (Prod.ext (funext fun w => ?_) ?_)⟩
  · show p w a = p w ((∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (Units.map (p w) a)) * finPartI L a : _root_.Neutral.B1.Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_single w]
    · show p w a = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w (p w a) w * 1
      simp
    · intro w' _ hw
      show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' (p w' a) w = 1
      exact Pi.mulSingle_eq_of_ne hw.symm _
    · simp
  · show q a = q ((∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (Units.map (p w) a)) * finPartI L a : _root_.Neutral.B1.Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_one, one_mul]
    · rfl
    · exact fun _ _ => rfl


open Classical in
theorem finite_order_of_inf_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : _root_.Formalism.L2.Host.HChar L),
    (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  intro L _ _ χ h
  obtain ⟨hfin, hlev⟩ := GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, _root_.Formalism.L2.Host.IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    refine hn _ ?_ (hx x hu)
    show Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L)) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hu, one_pow]
  choose m hm0 hm using hm
  set M := ∏ v ∈ hfin.toFinset, m v with hM
  have hM0 : 0 < M := Finset.prod_pos fun v _ => hm0 v
  have hloc : ∀ v x, _root_.Formalism.L2.Host.IsUnitAt v x → χ.loc v x ^ M = 1 := by
    intro v x hx
    by_cases hv : χ.UnrAt v
    · rw [hv x hx, one_pow]
    · obtain ⟨d, hd⟩ : m v ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
      rw [hd, pow_mul, hm v x hx, one_pow]
  have hunit : ∀ a ∈ unitIdl L, (χ ^ M).1 a = 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_decomp a
    have h1 : (χ ^ M).1 (finPartI L a) = 1 := by
      refine GlobalTheory.Mem.LocTriv.eq_one_of_local L _ (χ ^ M).2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v x hx => ?_
      refine hloc v x ?_
      show Valued.v (x : v.adicCompletion L) = 1
      rw [hx]
      exact ha v
    have h2 : (χ ^ M).1 (∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (u w)) = 1 := by
      show χ.1 _ ^ M = 1
      rw [triv_inf χ h, one_pow]
    rw [hu, map_mul, h1, h2, one_mul]
  have hle : unitIdl L ⊔ (_root_.Neutral.B1.diagUnits L).range ≤ (χ ^ M).1.ker := by
    refine sup_le hunit ?_
    rintro _ ⟨k, rfl⟩
    exact (χ ^ M).2.2 k
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨M * (unitIdl L ⊔ (_root_.Neutral.B1.diagUnits L).range).index, Nat.mul_pos hM0 (Nat.pos_of_ne_zero hfi.index_ne_zero), ?_⟩
  unfold _root_.Formalism.L2.Host.HChar.OrderDvd
  rw [pow_mul]
  refine Subtype.ext (MonoidHom.ext fun a => ?_)
  show (χ ^ M).1 a ^ _ = 1
  rw [← map_pow]
  exact hle (Subgroup.pow_index_mem _ a)

end GlobalTheory.Mem.FinOrder
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

namespace GlobalTheory.CxPtsDense

open GlobalTheory.CxPts

variable {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) (σ : F →+* ℂ)

theorem exists_param [GeometricallyIntegral p] [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : f ≠ 0) :
    ∃ (B : Type) (_ : TopologicalSpace B) (s : B → CxPts p σ), Nonempty B ∧ Continuous s ∧
      ptsIn p σ U ⊆ Set.range s ∧ Dense (s ⁻¹' ptsIn p σ (X.basicOpen f)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F ℂ := σ.toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have : Nontrivial Γ(X, U) := nontrivial_of_ne _ _ hf
  have : NoZeroDivisors (ℂ ⊗[F] Γ(X, U)) :=
    @UnitRigidity.noZeroDivisors_tensor F Γ(X, U) _ _ _ (algX p U).toAlgebra X p _
      hU.fromSpec (inferInstanceAs (IsOpenImmersion hU.fromSpec)) hg ℂ _ _
  have hinj := Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := Γ(X, U))
      (algebraMap F ℂ).injective
  have : Nontrivial (ℂ ⊗[F] Γ(X, U)) := hinj.nontrivial
  have : IsDomain (ℂ ⊗[F] Γ(X, U)) := NoZeroDivisors.to_isDomain _
  let φ (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    q.toRingHom.comp (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (1 ⊗ₜ a) := rfl
  have hφ (q) (a : F) : φ q (algX p U a) = σ a := by
    have : ((1 : ℂ) ⊗ₜ[F] algX p U a) = algebraMap ℂ (ℂ ⊗[F] Γ(X, U)) (σ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := F) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, AlgHom.commutes]
    rfl
  let s (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : CxPts p σ := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p σ U a (s q) = q (1 ⊗ₜ a) := ev_ofHom _ _ _ a
  refine ⟨_, inferInstance, s, ?_, ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℂ ⊗[F] Γ(X, U))
    let := Ideal.Quotient.field m
    have : Module.Finite ℂ ((ℂ ⊗[F] Γ(X, U)) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
    exact ⟨(IsAlgClosed.lift (R := ℂ) (S := (ℂ ⊗[F] Γ(X, U)) ⧸ m) (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩
  · refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p σ U a ∘ s) := by
      have : ev p σ U a ∘ s = fun q => q (1 ⊗ₜ a) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  · let ψ : Γ(X, U) →ₐ[F] ℂ :=
      { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
    let q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
    refine ⟨q, Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q) hy fun a => ?_)⟩
    refine (hsv q a).trans ?_
    simp only [q, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  · have hf' : ((1 : ℂ) ⊗ₜ[F] f) ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq

theorem exists_ne_zero_basicOpen_le [IsIntegral X] {U W : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ X.basicOpen f ≤ W := by
  obtain ⟨x, hxU, hxW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hne hW
  obtain ⟨f, hfW, hf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  refine ⟨f, ?_, hfW⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hf
  exact hf

theorem nonempty_and_dense_of_geometricallyIntegral [GeometricallyIntegral p] [LocallyOfFiniteType p] :
    Nonempty (CxPts p σ) ∧ ∀ W : X.Opens, (W : Set X).Nonempty → Dense (ptsIn p σ W) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  refine ⟨?_, fun W hW y => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    obtain ⟨f, hf, -⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ ⟨_, hx⟩
    obtain ⟨B, _, s, ⟨b⟩, -⟩ := exists_param p σ hU hf
    exact ⟨s b⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
    obtain ⟨f, hf, hfW⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
    obtain ⟨B, _, s, -, hs, hr, hd⟩ := exists_param p σ hU hf
    obtain ⟨b, rfl⟩ := hr (mem_ptsIn.2 hx)
    exact closure_mono (ptsIn_mono hfW) (hs.closure_preimage_subset _ (hd b))

theorem nonempty_and_dense : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ),
    Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) :=
  fun _ _ Y σ => nonempty_and_dense_of_geometricallyIntegral Y.str σ

end GlobalTheory.CxPtsDense
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

namespace GlobalTheory.BijPointsIso

universe u

variable {X Y : Scheme.{u}}

theorem universallyInjective_of_injective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro z
  let K := AlgebraicClosure ((pullback f f).residueField z)
  let φ : Spec (.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫
      (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
    h K (by simp only [Category.assoc, pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hφ₁]
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨(φ ≫ pullback.fst f f) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem surjective_of_surjective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Surjective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    Function.Surjective f := by
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨g, hg⟩ := h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
    Y.fromSpecResidueField y)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨g pt, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  simp only at hg
  rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem bijective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (hR : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩
  change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e
  rw [Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot,
    sub_eq_zero] at e
  exact e

theorem isIso_stalkMap_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [UniversallyInjective f] [IsDominant f]
    (hc : CharZero (Y.residueField (f (genericPoint X)))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  set x := genericPoint X
  have h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective.{u} f).out 1 3).mp ‹_›
  have hpi := h3.2 x
  have hr : Function.Bijective (f.residueFieldMap x) := by
    algebraize [(f.residueFieldMap x).hom]
    have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hpi
    exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _
  have hX : IsField (X.presheaf.stalk x) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f x)) := by
    rw [GlobalTheory.apply_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  have hsq := Scheme.residue_residueFieldMap f x
  have hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm
  have bX := bijective_residue_of_isField hX
  have bY := bijective_residue_of_isField hY
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (X.residue x ∘ f.stalkMap x) := by
    have e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x)) := funext hsq'
    rw [e]; exact hr.comp bY
  exact (Function.Bijective.of_comp_iff' bX _).mp this

end GlobalTheory.BijPointsIso

namespace GlobalTheory.BijPointsIso

theorem charZero_residueField {F : Type} [Field F] [CharZero F] (Y : Var F) (y : Y.X) :
    CharZero (Y.X.residueField y) := by
  let ψ : F →+* Y.X.residueField y :=
    (Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))
  exact charZero_of_injective_ringHom ψ.injective

theorem isIso_of_bijective_points : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F)
    (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str →
      (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) →
        IsIso h := by
  intro F _ _ Y₁ Y₂ h hc hb
  have : UniversallyInjective h :=
    universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1
  have : IsProper (h ≫ Y₂.str) := hc ▸ inferInstance
  have : IsProper h := IsProper.of_comp h Y₂.str
  have hs : Function.Surjective h := surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2
  have : IsDominant h := ⟨hs.denseRange⟩
  have := isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)
  have hN := Y₂.isNormalScheme
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk

end GlobalTheory.BijPointsIso
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory


noncomputable section
namespace GlobalTheory.CoordReduce



open ReciprocityTheory.ChartRestriction.G.Out in
theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

end GlobalTheory.CoordReduce
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_unique_stepRel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  intro F E _ _ _ _ _ σ hcm d b s M J x a B J' μ' hM hsd hμ'
  have : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨ν, hν, hνu⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hcm d b s (M + 1) J a (by omega) hsd.1 hsd.2.1
  obtain ⟨-, ⟨e, he, heu⟩, hcont⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hcm (AF F) M J x a B J' hsd
  obtain ⟨-, hinv, horb, hfin, hne⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hcm d b s (M + 1) J x a ν hsd.1 hsd.2.1 hsd.2.2.1 hν
  obtain ⟨hc1, hc2⟩ := hcont e he
  constructor
  · have : (μ'.map e.symm).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ' e.symm hc2 hc1
    obtain ⟨μ, hμ, hint⟩ := GlobalTheory.T.weil_formula_haar_orbit_stabilizer (HA (AF F) σ J) (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)
      (ratTup (F := F) (AF F) x) (μ'.map e.symm) ν this hfin hne hinv horb
    refine ⟨μ, hμ, fun ν' hν' e' he' => ?_⟩
    obtain rfl := hνu ν' hν'
    obtain rfl := heu e' he'
    exact hint
  · intro μ₁ μ₂ h₁ h₂
    have k₁ := h₁ ν hν e he
    have k₂ := h₂ ν hν e he
    classical
    let t : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
      if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y then h.choose else 1
    have ht : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
        t y • ratTup (F := F) (AF F) x = y := fun y hy => by
      simp only [t, dif_pos hy]
      exact hy.choose_spec
    exact Measure.ext_of_lintegral _ fun f hf => (k₁ f hf t ht).trans (k₂ f hf t ht).symm

end GlobalTheory.GaugeEx
end
