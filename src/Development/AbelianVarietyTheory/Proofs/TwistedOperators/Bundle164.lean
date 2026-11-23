module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle093
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix

namespace GlobalTheory.GelfandKazhdan

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

variable [TopologicalSpace G]

theorem isAdmissible_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (h : IsAdmissible π) : IsAdmissible (π.comp φ : Representation ℂ G V) := by
  have e0 : (φ : G → G) = Φ := funext fun x => (hΦ x).symm
  have hc : Continuous φ := e0 ▸ Φ.continuous
  have ho : IsOpenMap φ := e0 ▸ Φ.isOpenMap
  refine ⟨fun v => (h.1 v).preimage hc, fun K hKo hKc => ?_⟩
  have e : fixed (π.comp φ : Representation ℂ G V) K = fixed π (K.map φ) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (ho _ hKo) (hKc.image hc)

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

theorem smoothTrace_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (hμ : μ.map Φ = μ) (h : IsAdmissible π) {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    smoothTrace (π.comp φ : Representation ℂ G V) μ (f ∘ Φ) = smoothTrace π μ f := by
  have h' := isAdmissible_comp φ Φ hΦ h
  unfold smoothTrace
  congr 1
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [h'.1.map_smoothOp (hf.comp_continuous Φ.continuous) (hc.comp_homeomorph Φ), h.1.map_smoothOp hf hc]
  conv_rhs => rw [← hμ]
  rw [Φ.measurableEmbedding.integral_map]
  simp [hΦ]

theorem smoothTrace_conj [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {π : Representation ℂ G V}
    (h : IsAdmissible π) {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (g : G) :
    smoothTrace π μ (fun x => f (g * x * g⁻¹)) = smoothTrace π μ f := by
  let Φ : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  have hΦ : ∀ x, Φ x = φ x := fun _ => rfl
  have hμ : μ.map Φ = μ :=
    ((measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)).map_eq
  rw [← smoothTrace_comp φ Φ hΦ hμ h hf hc]
  refine (h.smoothTrace_eq_of_equiv (isAdmissible_comp φ Φ hΦ h).1 (hf.comp_continuous Φ.continuous)
    (hc.comp_homeomorph Φ) ho hK
    (LinearEquiv.ofLinear (π g) (π g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])) fun x v => ?_).symm
  change π g (π x v) = π (g * x * g⁻¹) (π g v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

end General

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.SplitFlip

theorem invTranspose_invTranspose (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) :
    invTranspose n R (invTranspose n R g) = g :=
  Units.ext (transpose_transpose _)

theorem continuous_invTranspose (n : ℕ) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invTranspose n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem equiv_contra (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invTranspose n k)) (contra π)) := by
  borelize k
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  have hb : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
    intro U hU
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
    exact ⟨J, h1, isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩
  let μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n))
  haveI : μ.IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hinv := invTranspose_invTranspose n k
  have hcont := continuous_invTranspose n k
  let Ψ : GL (Fin n) k ≃ₜ* GL (Fin n) k :=
    { toFun := invTranspose n k, invFun := invTranspose n k, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul _, continuous_toFun := hcont, continuous_invFun := hcont }
  let Φ : GL (Fin n) k ≃ₜ GL (Fin n) k := Ψ.toHomeomorph
  have hΦ : ∀ x, Φ x = invTranspose n k x := fun _ => rfl
  have hμ : μ.map Φ = μ := by
    have : (μ.map Φ).IsHaarMeasure := Ψ.isHaarMeasure_map μ
    refine @eq_haarVol _ _ _ _ _ _ _ _ _ _ _ this _ isOpen_KO le_rfl ?_
    refine (Measure.map_apply (μ := μ) Φ.measurable isOpen_KO.measurableSet).trans ?_
    have e : Φ ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) = KO k (Fin n) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_KO_iff]
      exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩
    rw [e]
    exact haarVol_self isOpen_KO le_rfl
  obtain ⟨hca, hct⟩ := GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv _ μ hb V π ha
  let T : SB (GL (Fin n) k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => smoothTrace π μ φ.1
      map_add' := fun φ ψ => ha.smoothTrace_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 isOpen_KO isCompact_KO
      map_smul' := fun c φ => ha.smoothTrace_smul φ.2.1 φ.2.2 isOpen_KO isCompact_KO c }
  have hT := GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL k (Fin n) T fun g φ ψ h => by
    change smoothTrace π μ ψ.1 = smoothTrace π μ φ.1
    rw [show ψ.1 = _ from funext h]
    exact smoothTrace_conj ha isOpen_KO isCompact_KO φ.2.1 φ.2.2 g
  refine GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible _ μ hb V _ _ _ (isAdmissible_comp _ Φ hΦ ha) hca
    (isIrreducible_comp _ (fun g => ⟨_, hinv g⟩) hi)
    ((GlobalTheory.T.smoothContragredient_irreducible_and_reflexive _ hb V V π π ha ha).1 hi) fun f hf hc => ?_
  have h1 := hf.comp_continuous Φ.continuous
  have h2 := hc.comp_homeomorph Φ
  have h3 := smoothTrace_comp _ Φ hΦ hμ ha h1 h2
  rw [show (f ∘ Φ) ∘ Φ = f from funext fun x => congrArg f (hinv x)] at h3
  rw [h3, hct f hf hc]
  refine hT ⟨fun g => f g⁻¹, hf.comp_continuous continuous_inv, hc.comp_homeomorph (Homeomorph.inv _)⟩
    ⟨f ∘ Φ, h1, h2⟩ fun x y hxy => congrArg f ?_
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  change (x⁻¹).valᵀ * y.val = 1
  rw [hxy, ← transpose_mul, Units.mul_inv, transpose_one]

end GlobalTheory.GelfandKazhdan
end

section

noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {q n : ℕ}

theorem v_det_mat (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) : Valued.v (mat g).det = 1 := by
  have h : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h1 := congrArg (fun M => Valued.v (det M)) h
  have hJ : IsInt (antiJ L n) := fun i j => by
    unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  simp only [det_mul, map_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσ,
    v_det_eq_one hJ hJ GlobalTheory.UnitarySwap.antiJ_mul_self, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, h1])

theorem secVal_pow {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ) (k : ℕ) :
    secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = varX q n (χ ϖ) s ^ k := by
  have h := P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem section_eq (hC : Completion) {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ}
    {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n χ s Φ) (g : GU σ n) {l : ℕ} (h : HasLen (mat g) l) :
    Φ (io1 σ n g) = varX q n (χ ϖ) s ^ l := by
  obtain ⟨U, V, C, hfr, hdet⟩ := h
  obtain ⟨k, hk, hk', hx⟩ := hC L ϖ σ q n hU g U V C hfr
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hK : (⟨k, hk⟩ : GD σ n) ∈ KD σ n := ⟨hk, hk'⟩
  have hp : ∀ x : Fin n → L, ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv ((mat g * C) *ᵥ x) ((mat g * C) *ᵥ x) := fun x => by
    change (blkMat finSumFinEquiv (mat g) 1 * k.1) *ᵥ _ = _
    rw [← mulVec_mulVec, hx, blkMat_mulVec, mulVec_mulVec, one_mulVec]
  have hP : io1 σ n g * ⟨k, hk⟩ ∈ PD σ n := mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
    rw [hp, pairVec_mem_diagSub])
  have hlev : leviMat finSumFinEquiv ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 = mat g * C := by
    refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
    have := congrFun ((mem_siegelOf.1 hP).mulVec_diag (Pi.single j 1)) (finSumFinEquiv (.inl i))
    rw [hp, pairVec_inl, pairVec_inl] at this
    exact this.symm
  have h1 := hΦ ⟨_, hP⟩ _ (inv_mem hK)
  rw [mul_inv_cancel_right] at h1
  have h2 : Valued.v ((aD σ n ⟨_, hP⟩ * (ϖ ^ l)⁻¹ : Lˣ) : L) = 1 := by
    have hϖ : Valued.v (ϖ : L) = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
    rw [Units.val_mul, val_aOf, hlev, det_mul, map_mul, map_mul, v_det_mat hU.2.1, hdet, one_mul,
      Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, hϖ, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  rw [h1, ← inv_mul_cancel_right (aD σ n ⟨_, hP⟩) (ϖ ^ l), secVal_mul hq, secVal_unit q hχ _ h2, one_mul, secVal_pow hU]

theorem closedForm_eq {q : ℕ} (hq : q ≠ 0) (n m : ℕ) (ε s : ℂ) (α : Fin (n / 2) → ℂˣ) (hε : ε = (-1) ^ m) :
    closedForm q n (varX q n ε s) (varY q ε s) α = stdL q n α ε (s + 1 / 2) / dFac q n m s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h1 : ε * ((q ^ 2 : ℕ) : ℂ) ^ (-(s + 1 / 2)) = varY q ε s := by
    rw [varY, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    congr 2
    push_cast
    ring
  have h2 : (dFac q n m s)⁻¹ = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * varX q n ε s) := by
    rw [dFac, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [etaL, inv_inv, varX, hε, show -(2 * s + n - j) = (j : ℂ) + -(2 * s + n) by ring, Complex.cpow_add _ _ hq0,
      Complex.cpow_natCast, neg_pow (q : ℂ), pow_add]
    ring
  rw [div_eq_mul_inv, h2, stdL, h1, closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm (varY q ε s)]
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

theorem unramDoublingInert : UnramDoublingInert := by
  intro L _ _ _ ϖ σ q n hU _ _ μ _ hμ χ hχ s Φ hΦ α w hw
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hF : FracExists := T.matrixLengthExists_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq T.doubledLattice_primitive_isotropic_frame_completion hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small T.unitary_rank_le_one_integral_points hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (T.leviRadicalProductLength_of_lattice_steps T.lattice_add_vector_det_valuation T.dual_inter_eq_sum' T.blockTriangular_row_lattice_triangular_basis T.unitary_heisenberg_radical_coordinates)
      (T.smallRadicalCosetCount_of_heisenberg T.unitary_heisenberg_radical_coordinates (T.integralLatticeInverseIndex_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued) T.traceZero_integers_index_in_uniformizer_multiples) (T.small_corner_of_heisenberg_duality T.unitary_heisenberg_radical_coordinates T.dual_inter_eq_sum') T.length_count_generating_series_formula (T.unitaryIwasawaCosetSurj_of_leviElementExists T.exists_unitary_block_diagonal_levi_element)
      T.unitary_iwasawa_cells_disjoint T.exists_unitary_block_diagonal_levi_element (T.sphericalInductionTransitivity_of_leviExists T.exists_unitary_block_diagonal_levi_element) T.unitary_rank_le_one_integral_points T.unitary_levi_summation_geometric_series hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (T.biInvariant_replace_same_double_coset_sums _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.InertZeta

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_local_products_tendsto_frameStabiliser : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)), ∀ g ∈ GfC V, finE V g ∈ St β → ∃ γ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, Filter.Tendsto γ Filter.atTop (nhds g) ∧ ∀ s, γ s ∈ Subgroup.closure {k : GA D V | k ∈ GfC V ∧ finE V k ∈ St β ∧ ∃ v ε, IsPlaceIdem D v ε ∧ SuppPl ε V k} ∧ ∀ v ∈ s, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V (γ s) i j = algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V g i j := by
  first | exact @GlobalTheory.LocalApprox.exists_local_approx | exact GlobalTheory.LocalApprox.exists_local_approx | (intros; apply GlobalTheory.LocalApprox.exists_local_approx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ENNReal

namespace GlobalTheory.ConvGrowth

open GlobalTheory.AutomorphicL2Unitary

theorem lintegral_sq_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : L2 Γ μ) :
    ∫⁻ z in S, ‖lift Γ F z‖ₑ ^ (2 : ℝ) ∂μ ≤ N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  rw [← lintegral_indicator hS,
    lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hS),
    ← lintegral_const_mul'' _ ((Lp.aestronglyMeasurable F).enorm.pow_const _)]
  refine lintegral_mono fun q => ?_
  have e : ∀ γ : Γ, S.indicator (fun z => ‖lift Γ F z‖ₑ ^ (2 : ℝ)) ((γ : G) * q.out) =
      {γ : Γ | (γ : G) * q.out ∈ S}.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) γ := by
    intro γ
    by_cases hγ : (γ : G) * q.out ∈ S
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ,
        Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
  rw [tsum_congr e, ← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  exact hN _

theorem norm_convR_le_height : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  intro D V μ _ _ Ω hΩ ⟨A, C, hC⟩
  refine ⟨A, (μ Ω ^ (1 / 2 : ℝ)).toReal * Real.sqrt (max C 0), ?_⟩
  intro f' hf' hsupp M hM F g
  set b : ℝ := Real.sqrt (max C 0) * GlobalTheory.Grow.height V g ^ A with hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hh : 0 ≤ GlobalTheory.Grow.height V g := zero_le_one.trans (GlobalTheory.Grow.one_le_height V g)
  have hb0 : 0 ≤ b := by positivity
  set S : Set (GA D V) := (g * ·) '' Ω with hSdef
  have hSc : IsCompact S := hΩ.image (continuous_const_mul g)
  have hS : MeasurableSet S := hSc.isClosed.measurableSet
  have hcount : ∀ x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ S}.encard ≤ ENNReal.ofReal b ^ 2 := by
    intro x
    obtain ⟨hfin, hle⟩ := hC g x
    rw [← hfin.cast_ncard_eq, ← ENNReal.ofReal_pow hb0]
    have e : b ^ 2 = max C 0 * GlobalTheory.Grow.height V g ^ (2 * A) := by
      rw [hb, mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm A 2]
    rw [e]
    calc (((({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞)
        = ENNReal.ofReal ({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  set φ : GA D V → ℂ := GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F with hφ
  have hm : AEStronglyMeasurable φ μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have hmp : MeasurePreserving (g * ·) (μ.restrict Ω) (μ.restrict S) := by
    have := (measurePreserving_mul_left μ g).restrict_preimage_emb (measurableEmbedding_mulLeft g) S
    rwa [hSdef, preimage_image_eq _ (mul_right_injective g)] at this
  have hm' : AEStronglyMeasurable (φ ∘ (g * ·)) (μ.restrict Ω) :=
    hm.restrict.comp_measurePreserving hmp

  have h1 : ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' φ g‖ₑ ≤ ENNReal.ofReal M * eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hΩ.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, enorm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM y)
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)]
      simp
    exact hm'

  have h2 : eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) ≤ eLpNorm φ 2 (μ.restrict S) * μ Ω ^ (1 / 2 : ℝ) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm').trans (le_of_eq ?_)
    rw [eLpNorm_comp_measurePreserving hm.restrict hmp, Measure.restrict_apply_univ]
    norm_num

  have h3 : eLpNorm φ 2 (μ.restrict S) ≤ ENNReal.ofReal b * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    calc (∫⁻ z in S, ‖φ z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal b ^ 2 * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_sq_le (GQ V) μ hS _ hcount F) (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have hE := h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 zero_le))
    zero_le)
  have hμ : μ Ω ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ.measure_lt_top.ne
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal b * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) * μ Ω ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hμ)
  have := ENNReal.toReal_mono hfin hE
  rw [toReal_enorm] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0,
    ENNReal.toReal_ofReal hb0, ← Lp.norm_def, hb]
  ring

end GlobalTheory.ConvGrowth
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.LFun.ConjParam.satU_star_eq | exact GlobalTheory.LFun.ConjParam.satU_star_eq | (intros; apply GlobalTheory.LFun.ConjParam.satU_star_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.enorm_mixedModelTerm_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  first | exact @GlobalTheory.MixedTerm.enorm_term_le_iSup | exact GlobalTheory.MixedTerm.enorm_term_le_iSup | (intros; apply GlobalTheory.MixedTerm.enorm_term_le_iSup <;> assumption)
end
