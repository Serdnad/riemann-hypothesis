module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

private theorem cj_val {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : cj M M.val x = x := by
  exact cj_mem M.val h

private theorem emb_mem_Qbar (D : D7) (e : D.host.E →+* ℂ) (x : D.host.E) : e x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ (e.toRatAlgHom x) := hx.algHom _
  exact mem_algebraicClosure_iff.mpr this

private theorem differentiable_U1 (Λ : AddSubgroup ℂ) (ω : ℂ) {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U1 Λ ω G) := by
  unfold U1
  fun_prop

private theorem U_pullB_eq_prod (D : D7) (h : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) (g : ℂ → ℂ) (t : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) = fun z =>
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  have hP := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.1
  funext z
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · simp only [coordB_add]
  · congr 1
    change _ = ∑ j, (_ / (area (tor0 D cc δ).abelian₂ : ℂ) - _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ)))
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem translates_coef_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, Differentiable ℂ F ∧ CoefIn D F Qbar := by
  intro D cc δ hC N N' r b hb F hF
  have h : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D h cc δ hC).1
  have hσ : Differentiable ℂ (sgStar (lamOf D cc δ)) := (GlobalTheory.OddTheta.sgStar_laws _ hlat).1.1
  have hL := (GlobalTheory.OnCoord.coords_of_orthonormal_basis D h cc δ N N' r b hb).2.2.2.1
  unfold Tr at hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨t, ⟨m, hm, hmt⟩, rfl⟩ := hF
    change Differentiable ℂ (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) ∧
      CoefIn D (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) Qbar
    rw [U_pullB_eq_prod D h cc δ hb]
    have hq : ∀ j, InRationalLattice (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) := fun j => by
      refine ⟨m, hm, ?_⟩
      rw [← coordB_smul, Nat.cast_smul_eq_nsmul]
      exact (hL _).1 hmt j
    have hl : ∀ j τ a c, (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)) ∈ Qbar := fun j τ a c => by
      change (starRingEnd ℂ) (embT D τ (b j a c)) ∈ Qbar
      rw [← emb_conj]
      exact emb_mem_Qbar D _ _
    have key := GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj D N N' r Qbar Qbar.val
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j => U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) (sgStar (lamOf D cc δ)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j τ a c => (starRingEnd ℂ) ((tor0 D cc δ).emb τ (b j a c)))
      (fun j => differentiable_U1 _ _ hσ) (fun j => differentiable_U1 _ _ hσ)
      (fun j n => by
        have := (GlobalTheory.T.forall_use1 D cc δ hC).1 _ (hq j) n
        exact ⟨this, (cj_val this).symm⟩)
      (fun j τ a c => ⟨hl j τ a c, (cj_val (hl j τ a c)).symm⟩)
    exact ⟨key.1, fun α => (key.2.2 α).1⟩
  | zero => exact ⟨differentiable_const 0, fun α => by rw [taylor_zero]; exact zero_mem _⟩
  | add F G _ _ hF hG =>
    exact ⟨hF.1.add hG.1, fun α => by
      rw [taylor_add D hF.1 hG.1]; exact add_mem (hF.2 α) (hG.2 α)⟩
  | smul c F _ hF =>
    have : c • F = fun z => (c : ℂ) * F z := rfl
    rw [this]
    exact ⟨hF.1.const_mul _, fun α => by
      rw [taylor_mul D _ hF.1]; exact mul_mem c.2 (hF.2 α)⟩

end GlobalTheory.ThetaConj
end
end

section

noncomputable section

namespace GlobalTheory.StdFrame

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OrthFrame (V : HSpace E) : Prop :=
  (∀ a b, V.hT (V.frame a) (V.frame b) = if a = b then 1 else 0) ∧ ∀ a, V.frame a ∈ V.L0

theorem OrthFrame.gram_eq {V : HSpace E} (h : OrthFrame V) : V.gram = 1 := by
  ext a b
  rw [Matrix.one_apply]
  exact h.1 a b

theorem OrthFrame.mem_iff {V : HSpace E} (h : OrthFrame V) (x : Fin V.rank → E) :
    ∑ a, x a • V.frame a ∈ V.L0 ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx a
    have hd : ∑ a, x a • V.frame a ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 := by
      rw [V.baseLattice_isUnimodular]; exact hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hd
    have h1 : V.hT (V.frame a) (∑ b, x b • V.frame b) ∈ (1 : Submodule (𝓞 E) E) := hd _ (h.2 a)

    simpa [map_sum, map_smul, h.1] using h1
  · intro hx
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx a)
    rw [← ho, algebraMap_smul]
    exact V.L0.smul_mem o (h.2 a)

def reframe (V : HSpace E) (b : Module.Basis (Fin V.rank) E V.V) : HSpace E := { V with frame := b }

theorem exists_orthFrame (V : HSpace E) {n : ℕ} (hn : V.rank = n) (h : Formalism.HermitianLatticesTheory.IsOrthoLattice V.hT V.L0 n) :
    ∃ b, OrthFrame (reframe V b) := by
  subst hn
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  refine ⟨Module.Basis.mk h1 h2.ge, fun (a b : Fin V.rank) => ?_, fun (a : Fin V.rank) => ?_⟩
  · show V.hT (Module.Basis.mk h1 h2.ge a) (Module.Basis.mk h1 h2.ge b) = _
    rw [Module.Basis.mk_apply, Module.Basis.mk_apply, h4]
    rfl
  · show Module.Basis.mk h1 h2.ge a ∈ V.L0
    rw [Module.Basis.mk_apply, h3]
    exact Submodule.subset_span ⟨a, rfl⟩

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hLat_one {D : D7} (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem vStd_iff_gram_and_lattice (D : D7) (i : Fin D.R.m) :
    VStd D i ↔ (Vc D i).gram = 1 ∧
      L0c D (Vc D i) = ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) : Set (Fin (Vc D i).rank → D.host.E)) := by
  rw [VStd, hLat_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]

def FrameChoice (D : D7) (i : Fin D.R.m) : Prop := OrthFrame (D.sp.V ((i : ℕ) + 1))

theorem vStd_of_frameChoice : ∀ (D : D7) (i : Fin D.R.m), FrameChoice D i → VStd D i := by
  intro D i h
  refine (vStd_iff_gram_and_lattice D i).2 ⟨h.gram_eq, ?_⟩
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact (h.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem nV_pos (R : Ranks) : 0 < R.nV := by
  have := R.rank_add_five_le
  unfold Ranks.nV
  omega

theorem neg_eq_false_of_vStd (D : D7) (i : Fin D.R.m) (h : VStd D i) : D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  let τ := D.host.φ₀
  have hs := D.sp.V_sig ((i : ℕ) + 1) τ
  rw [factVSig _ _ D.sp _ (by omega) (by omega) τ, if_pos hneg] at hs
  have h1 : Formalism.UG.HasSignature ((Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)).map τ)
      (Vc D i).rank 0 := by
    have h0 : (Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)) = 1 := h.1
    rw [h0, Matrix.map_one _ (map_zero _) (map_one _)]
    simpa using Formalism.UG.P.stdform_sig_one (n := Fin (Vc D i).rank)
  have h2 := (sig_family (Vc D i) τ (D.sp.cm.cmUnram.2.1 τ) _ h1 hs).1
  have := nV_pos D.R
  simp only at h2
  omega

theorem neg_eq_false_of_posDef (D : D7) (i : Fin D.R.m) (h : (Vc D i).IsPosDef) :
    D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  have h1 := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) D.host.φ₀
  rw [if_pos hneg] at h1
  have h2 := congrArg Prod.snd ((h D.host.φ₀).symm.trans h1)
  exact (nV_pos D.R).ne h2

end GlobalTheory.StdFrame
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  first | exact @GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | (intros; apply GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idelicCharacter_trivial_baseFiniteIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  first | exact @GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | exact GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | (intros; apply GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem valued_natCast_le_of_mem_asIdeal {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (hm : (m : 𝓞 L) ∈ P.asIdeal) : Valued.v ((m : P.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((m : P.adicCompletion L)) = ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : P.adicCompletion L) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap L (P.adicCompletion L)) m).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

theorem finiteAdele_apply_sub_one_of_eq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (a b : FiniteAdeleRing (𝓞 L) L) (e : a - 1 = (m : FiniteAdeleRing (𝓞 L) L) * b) :
    a P - 1 = (m : P.adicCompletion L) * b P := by
  let ev : FiniteAdeleRing (𝓞 L) L →+* P.adicCompletion L :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) P
  have e3 : ev (a - 1) = ev ((m : FiniteAdeleRing (𝓞 L) L) * b) := congrArg ev e
  rw [ev.map_sub, ev.map_mul, ev.map_one, map_natCast ev m] at e3
  exact e3

theorem tame_heckeChar_eq_one_of_finUnit : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  intro D c χ hc ht m hu x hx ⟨y, hy, hxy⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating D ι h1 h2 (GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.T.finiteIdele_exists_local_approx' D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : IsUnitAt P (atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.loc P (atFin P (k P)) = 1 := by
    by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · refine ht P _ hun ?_
      have e : ι (finPart D (x : AE D)) - 1 = (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * ι y := by
        rw [← map_one ι, ← map_sub, hxy, map_nsmul, nsmul_eq_mul]
      have e2 : ι (finPart D (x : AE D)) P - 1 = (m : P.adicCompletion D.host.E) * ι y P :=
        finiteAdele_apply_sub_one_of_eq P m _ _ e
      have c1 : Valued.v (ι (finPart D (x : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
        rw [e2, map_mul]
        calc _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
              mul_le_mul' (valued_natCast_le_of_mem_asIdeal P m hm) ((h2 _).1 hy P)
          _ = _ := mul_one _
      have e4 : ((atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          (ι (finPart D (x : AE D)) P - 1) - (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4]
      exact Valuation.map_sub_le _ c1 b'
    · exact hu P hm _ hun
  show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory
end
