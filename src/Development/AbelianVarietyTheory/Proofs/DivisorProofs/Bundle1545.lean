module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.placeIdempotent_smul_mem_completedSelfDualLattice : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V := by
  first | exact @GlobalTheory.IdemLat.lamHat_idem | exact GlobalTheory.IdemLat.lamHat_idem | (intros; apply GlobalTheory.IdemLat.lamHat_idem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Vec

section Mat

open Matrix
open scoped ComplexOrder

theorem exists_isONBasis {n P Q : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s)
    (hs : Formalism.UG.HasSignature G P Q) : ∃ B : Matrix (Fin n) (Fin n) ℂ, IsONBasis G s B P := by
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hn : p + q = n := by
    have e := Matrix.trace_mul_comm B B'
    rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e
    exact_mod_cast e.symm
  subst hn
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  have hsig : Formalism.UG.HasSignature G p q := by
    refine ⟨e.symm, ⟨B.submatrix e id, B'.submatrix id e, ?_, ?_⟩, ?_⟩
    · have : B.submatrix e id * B'.submatrix id e = (B * B').submatrix e e := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, h1, Matrix.submatrix_one_equiv]
    · rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_id_id]
    · rw [Formalism.UG.P.cT_conj_eq, Matrix.reindex_apply, Equiv.symm_symm]
      show (B.submatrix e id)ᴴ * G.submatrix e e * B.submatrix e id = _
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h3,
        Matrix.submatrix_id_id]
      rfl
  obtain ⟨rfl, -⟩ := Formalism.UG.P.signature_unique _ G _ _ _ _ hsig hs
  let ε : Fin (p + q) → ℝ := fun a => Sum.elim (fun _ => 1) (fun _ => -1) (e.symm a)
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e.symm e.symm =
      Matrix.diagonal fun a => (ε a : ℂ) := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [ε, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  refine ⟨B.submatrix id e.symm, ε, fun a => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective a
    rcases a with a | a
    · exact Or.inl ⟨by simp [ε], by simp [e]⟩
    · exact Or.inr ⟨by simp [ε], by simp [e]⟩
  · rw [← hd, ← h3]
    rfl
  · rw [← hd, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M id e.symm) h4

theorem isCartanInv_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

end Mat

variable {D : D7}

theorem theta_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  let H : WO S T → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun w =>
    { toFun := heisO ψ S T w
      map_add' := fun a b => funext fun x => mul_add _ _ _
      map_smul' := fun a b => funext fun x => mul_left_comm _ _ _ }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.pi fun w => l ∘ₗ H w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((H x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((H y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

theorem theta_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) :=
  (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.GalLift.Vec

end
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.EtaSignReal

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_signToCircle [Algebra.IsQuadraticExtension F E] (η : (AF F)ˣ →* Circle) (hη : IsEtaF E η) :
    η = signToCircle.comp (normSign E) := by
  obtain ⟨-, h1, h3, h4⟩ := hη
  refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
  obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
  exact h1 t

theorem finComp_eq_one {a : (AF F)ˣ} (ha : At (evI F) ((a : AF F) - 1)) : finComp a = 1 := by
  have h := ha ((0 : Ainf F), (1 : Af F)) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : ((a : AF F) - 1).2 = 0 := by
    have := congrArg Prod.snd h
    change (1 : Af F) * ((a : AF F) - 1).2 = 0 at this
    rwa [one_mul] at this
  have h3 : (a : AF F).2 = 1 := sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)
  funext v
  apply Units.ext
  change (a : AF F).2 v = 1
  rw [h3]
  rfl

theorem normSign_eq_prod [Algebra.IsQuadraticExtension F E] {a : (AF F)ˣ} (ha : finComp a = 1) :
    normSign E a = ∏ w : InfinitePlace F, eta F E w.Completion (infComp a w) := by
  change etaProd F E (finComp a) (infComp a) = _
  rw [etaProd, ha]
  have : ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1 :=
    fun v => eta_eq_one_iff.2 (one_mem _)
  simp only [this, finprod_one, one_mul]

theorem ringEquivReal_neg {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) {δ : F} (hδ : δ ≠ 0) {θ : E} (hθ : σ θ = -θ) (h1 : θ * θ = algebraMap F E δ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion δ) < 0 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set z := τ.1 θ
  have hz : star z = -z := by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]
  have hre : z.re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ := by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe]
      rfl
    rw [h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr
  have hne : e (algebraMap F w.Completion δ) ≠ 0 := (map_ne_zero e).2 ((map_ne_zero _).2 hδ)
  refine lt_of_le_of_ne ?_ hne
  rw [hr]
  nlinarith [mul_self_nonneg z.im]

theorem mem_normGroup_iff_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) (x : (w.Completion)ˣ) :
    x ∈ normGroup F E w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    haveI := hcm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])
  obtain ⟨δ, b, hδ, h0, hσb, h1⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg := ringEquivReal_neg hcm hw τ hδ0 hσb h1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨p, q, h⟩
    have hx0 : e (x : w.Completion) ≠ 0 := (map_ne_zero e).2 x.ne_zero
    have h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2 := by
      rw [h, map_sub, map_mul, map_pow, map_pow]
    refine lt_of_le_of_ne ?_ hx0.symm
    rw [h2]
    nlinarith [sq_nonneg (e p), sq_nonneg (e q)]
  · intro hpos
    refine ⟨e.symm (Real.sqrt (e x)), 0, ?_⟩
    apply e.injective
    simp [Real.sq_sqrt hpos.le]

theorem piInf_idFF {w : InfinitePlace F} (hw : w.IsReal) (τ : EmbOver E w) (a : (AF F)ˣ) :
    piInf τ ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion) : ℝ) : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  change infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  rfl

theorem eta_eq_prod_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]

end GlobalTheory.EtaSignReal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjInner

theorem inner_eq_integral {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (c : ℂ)
    (h : ∀ x y, inner ℂ x y = c * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    inner ℂ x y = c * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hd : ∀ z : H, ∃ a, IsMultIP M μ 𝓕 (e z) (e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  have h1 := (ipM_spec M μ 𝓕 _ _ ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩ v v).2
  rw [h, h1, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

theorem conj_integral {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℂ) (hq : starRingEnd ℂ q = q) {a b a' b' : X → ℂ}
    (ha : ∀ g, a g = starRingEnd ℂ (a' g)) (hb : ∀ g, b g = starRingEnd ℂ (b' g)) :
    q * ∫ g, star (a g) * b g ∂μ = starRingEnd ℂ (q * ∫ g, star (a' g) * b' g ∂μ) := by
  rw [map_mul, hq, ← integral_conj]
  congr 2
  funext g
  rw [ha, hb, map_mul]
  rfl

theorem inner_conj_of_span {L W H H' : Type} [Field L] [AddCommGroup W] [Module L W] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : L →+* ℂ) (j : W →ₛₗ[σ] H)
    (j' : W →ₛₗ[(starRingEnd ℂ).comp σ] H') (s : Set W) (hs : Submodule.span L s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ) (x y : W) :
    ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ := by
  have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_right, inner_add_right, map_add (f := _), h1, h2]
    | smul a y _ h1 =>
      rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]
  | zero => simp
  | add x z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, map_add (f := _), h1, h2]
  | smul a x _ h1 =>
    rw [map_smulₛₗ, map_smulₛₗ, inner_smul_left, inner_smul_left, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]

theorem dim_conj {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt W ((starRingEnd ℂ).comp σ) ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  refine Finset.prod_congr rfl fun ρ _ => ?_
  unfold kapAt
  rw [GlobalTheory.ConjEval.lab_conj]

theorem dim_real {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _



theorem inner_conj_of_values {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (he : R.models_HW) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) {v : (R.MW i σ).Vec} {v' : (R.MW i ((starRingEnd ℂ).comp σ)).Vec} (hv : IsUnitV v) (hv' : IsUnitV v')
    {x y : (R.HW i σ).H} {x' y' : (R.HW i ((starRingEnd ℂ).comp σ)).H}
    (hx : ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ v' x' g))
    (hy : ∀ g, evAt R i σ v y g = starRingEnd ℂ (evAt R i _ v' y' g)) :
    ⟪x, y⟫_ℂ = starRingEnd ℂ ⟪x', y'⟫_ℂ := by
  have h1 := inner_eq_integral (R.MW i σ) (R.νW i) (R.fdW i) (R.HW i σ).e _ (he i σ).2.2 v hv x y
  have h2 := inner_eq_integral (R.MW i _) (R.νW i) (R.fdW i) (R.HW i _).e _ (he i _).2.2 v' hv' x' y'
  rw [dim_conj] at h2
  exact h1.trans ((conj_integral _ _ (dim_real _ σ) hx hy).trans (congrArg (starRingEnd ℂ) h2).symm)


end GlobalTheory.ConjInner
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_character_embedding_compat : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k : GA D (Wc D i), Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ T.Kf ((i : ℕ) + 1) σ := by
  first | exact @GlobalTheory.LiftLevel.isLift_one_iff_mem_level | exact GlobalTheory.LiftLevel.isLift_one_iff_mem_level | (intros; apply GlobalTheory.LiftLevel.isLift_one_iff_mem_level <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_level_action_cusp_form_representation : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.LevelRep.exists_cusp_rep | exact GlobalTheory.LevelRep.exists_cusp_rep | (intros; apply GlobalTheory.LevelRep.exists_cusp_rep <;> assumption)
end
