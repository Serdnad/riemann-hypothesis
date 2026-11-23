module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.RatioJoints.IsRatioAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Formalism.LocalToGlobal.Columns.Bundle016
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.JointsTrue

open _root_.Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR



theorem isDetLift_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Theta.AE D) (he : JoinChr.IsPlIdem D e P)
    (k : D.host.Eˣ) (y : Theta.AE D) (hy : Joints.IsRatioAt D e (k : D.host.E) y) (x : Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hx : ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Herm.Af D.host.F) = Joints.finE D y) :
    IsDetLift D.sp.cm x.1 (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
  let φ : Theta.AE D →+* AfE D.host.F D.host.E := Joints.finE D
  have hinc : ∀ a : D.host.E, φ (Theta.incA D a) = a ⊗ₜ[D.host.F] 1 := fun a => rfl
  have hc : ∀ z, φ (Theta.cA D z) = Formalism.UG.sigR D.sp.cm.sig _ (φ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [(Theta.cA D).map_zero, φ.map_zero, RingHom.map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [(Theta.cA D).map_add, φ.map_add, φ.map_add, ha, hb, RingHom.map_add (f := _)]
  have h1 : (finAf D.host.F D.host.E (Neutral.B1.localIdele _ P (Formalism.L2.Host.atFin P k)) : AfE D.host.F D.host.E) = φ (JoinChr.locE D e k) := by
    rw [GlobalTheory.Core.Cls.JointsStd.finAf_localIdele (e := φ e) (by rw [← φ.map_mul, he.1]) (fun a ha => ?_) k, JoinChr.locE, φ.map_add,
      φ.map_mul, φ.map_sub, φ.map_one, hinc]
    rw [he.2.2 a ha, ← hinc, ← φ.map_mul]
    exact not_congr (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _)
  have h2 := congrArg φ hy
  rw [φ.map_mul, hc, ← h1] at h2
  unfold IsDetLift h90
  rw [MonoidHom.div_apply, div_eq_iff_eq_mul]
  exact Units.ext (h2.symm.trans (by rw [Units.val_mul, hx]; rfl))


end GlobalTheory.Mem.JointsTrue

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.KMapHol

theorem exp_mem_kset {n : ℕ} (ε : Fin n → Bool) {X : Mt n} (hX : X ∈ lieH (Formalism.REAL.Jm ε))
    (hc : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have h1 : X ∈ lieH (1 : Mt n) := by
    show Xᴴ * 1 + 1 * X = 0
    rw [← hc.eq, ← Matrix.add_mul] at h0
    have := congrArg (· * (Formalism.REAL.Jm ε)⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.zero_mul] at this
    simpa using this
  have h2 : (NormedSpace.exp (t • X))ᴴ * 1 * NormedSpace.exp (t • X) = 1 := GlobalTheory.SmVec.exp_mem_UH isUnit_one h1 t
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by simpa [star_eq_conjTranspose] using h2), ?_⟩
  exact ((hc.smul_left t).exp_left).eq

theorem commute_conjH {n : ℕ} (ε : Fin n → Bool) {E : Mt n} (hc : Commute E (Formalism.REAL.Jm ε)) :
    Commute (conjH (Formalism.REAL.Jm ε) E) (Formalism.REAL.Jm ε) := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h1 : Formalism.REAL.Jm ε * Eᴴ = Eᴴ * Formalism.REAL.Jm ε := by
    have := congrArg conjTranspose hc.eq
    simpa only [conjTranspose_mul, (VKill.jm_herm ε).eq] using this
  have h2 : conjH (Formalism.REAL.Jm ε) E = -Eᴴ := by
    rw [conjH, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  rw [h2]
  exact Commute.neg_left h1.symm

theorem commute_single {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a = ε c) :
    Commute (Matrix.single a c (1 : ℂ)) (Formalism.REAL.Jm ε) := by
  show _ * _ = _ * _
  unfold Formalism.REAL.Jm
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.single_apply]
  split_ifs with h1 h2 h3 <;> simp_all

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem exists_form (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) (e : ∀ τ, lowT M τ)
    (τ : D.what₂.Tau) (x : GA D V) :
    ∃ ℓ : M.H τ →L[ℂ] ℂ, ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x := by
  let P := lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
  haveI : FiniteDimensional ℂ P := (h2 τ).1
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun y => U (Function.update e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩) x
      map_add' := fun y z => congrFun (U.map_update_add e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩ ⟨⟨z, h1 τ z.2⟩, z.2⟩) x
      map_smul' := fun a y => congrFun (U.map_update_smul e τ a ⟨⟨y, h1 τ y.2⟩, y.2⟩) x }
  refine ⟨(LinearMap.toContinuousLinearMap ℓ₀).comp P.orthogonalProjection, fun u => ?_⟩
  have : P.orthogonalProjection ((u : M.sm τ) : M.H τ) = ⟨_, u.2⟩ :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (K := P) ⟨_, u.2⟩
  rw [ContinuousLinearMap.comp_apply, this]
  rfl


open Classical in
theorem rder_eq (θ : InfFam D) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M)
    (hK : KEquiv θ M U) (e : ∀ τ, lowT M τ) (τ : D.what₂.Tau) (x : GA D V) (ℓ : M.H τ →L[ℂ] ℂ)
    (hℓ : ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x)
    {X Y : Mt V.rank} (hY : Y ∈ lieH (Formalism.REAL.Jm (M.ε τ))) (hc : Commute Y (Formalism.REAL.Jm (M.ε τ)))
    (hXY : X = (M.fr τ)⁻¹ * Y * M.fr τ)
    (hd : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ))
      (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) 0) :
    Rder θ V τ X (U e) x = ℓ (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) := by
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e1 : M.fr τ * X * (M.fr τ)⁻¹ = Y := by
    rw [hXY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one]
  have key : ∀ t : ℝ, U e (x * oneP θ V τ X t) = ℓ (M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ)) := by
    intro t
    have hk : M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
      rw [VKill.conj_exp hP, e1]; exact exp_mem_kset _ hY hc t
    have hm := (h2 τ).2.1 _ hk _ (e τ).2
    have h := hK τ _ hk e ⟨⟨_, h1 τ hm⟩, hm⟩ rfl
    have e2 : (M.fr τ)⁻¹ * (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) * M.fr τ = NormedSpace.exp (t • X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hPd, Matrix.mul_one]
    rw [e2] at h
    exact ((hℓ ⟨⟨_, h1 τ hm⟩, hm⟩).trans (congrFun h x)).symm
  unfold Rder
  simp only [key]
  exact ((ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd).deriv

theorem holAd_of_kEquiv : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  classical
  intro D θ V S M w hθ hS hw h1 h2 U hsm hK hp e hv g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => U e (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun τ => ((ModelRep.model_rep D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := hsm e k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := GlobalTheory.MultHol.lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show U e (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => U e (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => U e (g * L u)) u = Rder θ V τ X (U e) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show U e (g * L (u * _)) = _
      rw [hmul u hu _ (GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨hc, hU, -, hx⟩ := ModelRep.model_rep D V S M τ
    obtain ⟨-, hx⟩ := hx hS
    obtain ⟨hs, hk⟩ := VKill.borel_extVec D θ V S M w _ hθ hS hw hv τ
    have hk := hk a c hac
    rw [hx a c] at hk ⊢
    set a' := arr (nNeg (M.ε τ)) a with ha'
    set c' := arr (nNeg (M.ε τ)) c with hc'
    obtain ⟨p1, p2⟩ := GlobalTheory.MultHol.parts_mem_lieH (hG τ).1 (hG τ).2 ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ)
    by_cases hε : M.ε τ a' = M.ε τ c'
    · obtain ⟨ℓ, hℓ⟩ := exists_form h1 h2 U e τ (g * L u)
      obtain ⟨q1, q2⟩ := GlobalTheory.MultHol.parts_mem_lieH (VKill.jm_herm (M.ε τ)) (VKill.jm_det (M.ε τ)) (Matrix.single a' c' 1)
      have c1 := commute_single (M.ε τ) hε
      have c2 := commute_conjH (M.ε τ) c1
      have hcj : conjH (gramAt D V τ) ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ) =
          (M.fr τ)⁻¹ * conjH (Formalism.REAL.Jm (M.ε τ)) (Matrix.single a' c' 1) * M.fr τ := by
        rw [← M.fr_gram τ]; exact VKill.conjH_conj (M.fr_unit τ) _ _
      have hD := ((GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ (hG τ).1 (hG τ).2 hU).2 _ hs).2.1
      have r1 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q1 ((c1.add_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]) (hD _ p1).2
      have r2 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q2 ((c1.sub_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]) (hD _ p2).2
      have hk' := congrArg ℓ hk
      unfold dRepC at hk'
      rw [map_add (f := _), map_smul, smul_eq_mul] at hk'
      unfold derC
      rw [hder _ p1, hder _ p2, r1, r2, hk']
      split_ifs
      · rw [map_smul, hℓ (e τ), Function.update_eq_self, smul_eq_mul]
      · rw [map_zero]
    · obtain ⟨-, p, hpn, hεp⟩ := hS τ
      have hq := nNeg_shape hpn hεp
      have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
        intro b
        have := b.2
        rw [hεp, hq]
        unfold arr
        split_ifs with hb
        · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
        · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
      have hac' : (a : ℕ) ≤ c := hac
      have hne : a ≠ c := fun h => hε (by rw [ha', hc', h])
      rw [ha', hc', hsg, hsg, decide_eq_decide] at hε
      have ha : M.ε τ a' = false := by rw [ha', hsg]; simp only [decide_eq_false_iff_not]; omega
      have hb : M.ε τ c' = true := by rw [hc', hsg]; simp only [decide_eq_true_eq]; omega
      have h0 := congrFun (hp τ _ (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.single_mem_pMinus M τ ha hb) e) (g * L u)
      rw [if_neg hne]
      unfold derC
      rw [hder _ p1, hder _ p2]
      exact h0

end GlobalTheory.KMapHol
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section SameUp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem SameG.up' {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (q : 𝓞 X.E) {x : Sp X.E n}
    (hx : x ∈ p.1.1.deco.1.N) : SameG p (p.mv (p.1.1.deco.up P q x)) := by
  classical
  have hs : DecoSet.SameOn SG p.1.1.deco (p.1.1.deco.up P q x) :=
    DecoSet.sameOn_up _ P hP.ne (fun w hw => hP.sg ⟨w, hw⟩) q hx
  have hb : (p.1.1.deco.up P q x).1.be = p.1.1.deco.1.be := by
    unfold DecoSet.up
    split_ifs with h
    · rfl
    · rfl
  by_cases h : (∀ (w : Q) (z : Sp X.E n), p.1.1.1.2 w z ∈ (p.1.1.deco.up P q x).1.at w.1 ↔ z ∈ stdAt X.E n w.1) ∧ p.1.2 ∈ y.ys (p.1.1.deco.up P q x).1.N
  · have e : p.mv (p.1.1.deco.up P q x) = ⟨(⟨(p.1.1.deco.up P q x, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    exact ⟨rfl, rfl, fun w => hs w.1 w.2, hb⟩
  · have e : p.mv (p.1.1.deco.up P q x) = p := dif_neg h
    rw [e]
    exact SameG.refl p

end SameUp

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.cosetIn_rep_up (hX : B.fields.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv v c) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).upPt v c x))) =
      cosetIn ((I.stp u a i).rep c) := by
  by_cases hj : i + 1 = B.R.m
  · refine GStep.prefRep_eq_of_normal (I.stp0 u a i) c.1 (fun q' : (I.stp0 u a i).D c.1 => cosetIn q') (I.pref u a i c.1)
      (GStep.prefRep_normal (I.stp0 u a i) c.1 _ _ (fun p hp => hp.2.1 hj) (I.pref_of_normalFor u a i hj c.1)) c.2 _ fun h => ?_
    have r : SameG ((I.stp u a i).rep c) (((I.atIn u a).A i).upPt v c x) :=
      SameG.up' ((I.stp u a i).rep c) v (moveHyp_of_ok hPr u v) _ (Quotient.out x).2
    exact cosetIn_eq_of_sameG (R := B.R) (sel := I.sel) (mu := I.tup a) (cst := I.cst a)
      (u := u) (j := i) hX hPr
      (SameG.smul (Λ := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
        (Θ := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) h r)
  · have h0 : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn q = fun _ => ∅ := by
      intro q
      funext P
      have hq : q.1.2 = ∅ := by
        have := q.2
        rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
        exact this
      ext z
      simp [cosetIn, hq]
    exact (h0 _).trans (h0 _).symm

end GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem TC.up_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K → ∀ (v : (I.atT l u a).vT) (c : (I.chain l u a).cls i) (x : (I.fm l u a).lv i v c), (I.fm l u a).fv i v c x = 1 → chOf ((I.fm l u a).up i v c x) = chOf c := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K hR v c x _
  obtain ⟨k, hk⟩ := hR
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  let c' : (I.stp u a i).Cl := (I.stp u a i).cl c.1 (((I.atIn u a).A i).upPt v c x)
  change chOf c' = chOf c
  exact (hk.key c' c).2 ⟨rfl, I.cosetIn_rep_up hX l.pr u a i v c x⟩

end GlobalTheory.Mem.Col2
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.MemLat

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_N_iff (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal)
    (hcop : IsCoprime π (cO E π)) (x : Sp E n) :
    x ∈ d.N ↔ ∃ a ∈ d.L, ∃ b ∈ d.Lsh, x = a + cO E π • b := by
  constructor
  · intro hx
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • (π • x), d.L.smul_mem s (hd.smul_N_mem_L hmem hx), t • x, d.Lsh.smul_mem t (hd.N_le_Lsh hx), ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (cO E π) t, hst, one_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact d.N.add_mem (hd.L_le_N ha) (hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact hmem P) hb)

theorem std_of_gram (S : HSpace E) {m : ℕ} (h : S.rank = m) (hg : S.gram.reindex (finCongr h) (finCongr h) = 1) (x y : S.V) :
    stdH E m (Crd.co S h x) (Crd.co S h y) = S.hT x y := by
  subst h
  have hg' : ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hg a) b
    simpa [HSpace.gram, Matrix.one_apply] using this
  conv_rhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.sum_apply, hg',
  smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [stdH, Crd.co, starRingEnd_apply]

omit [NumberField E] in
theorem hStd_eq_stdH (x y : Fin n → E) : hStd E n x y = stdH E n x y := rfl

theorem mem_dual_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (b : S.V) :
    b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) (L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rw [mem_dual]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro H z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have := H a ha
    simpa [hStd_eq_stdH, hco] using this
  · intro H a ha
    have := H (co a) ⟨a, ha, rfl⟩
    simpa [hStd_eq_stdH, hco] using this

theorem companion_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (d : Deco E n ST SG) (hd : d.Ok)
    (hL : L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = d.L)
    (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) (y : S.V) :
    co y ∈ d.N ↔ ∃ a ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = a + star (algebraMap (𝓞 E) E π) • b := by
  have hA : ∀ a, a ∈ L ↔ co a ∈ d.L := fun a => by
    rw [← hL]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨z, hz, e⟩ => co.injective e ▸ hz⟩
  have hB : ∀ b, b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ d.Lsh := fun b => by
    rw [mem_dual_crd S co hco, hL]
    exact Iff.rfl
  have hc : ∀ v : Fin n → E, cO E π • v = star (algebraMap (𝓞 E) E π) • v := fun v => by
    rw [← algebraMap_smul E (cO E π) v, algebraMap_cO]
  rw [mem_N_iff d hd π hmem hcop]
  constructor
  · rintro ⟨a', ha', b', hb', e⟩
    refine ⟨co.symm a', (hA _).2 (by simpa using ha'), co.symm b', (hB _).2 (by simpa using hb'), co.injective ?_⟩
    rw [map_add (f := _), map_smul, co.apply_symm_apply, co.apply_symm_apply, e, hc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨co a, (hA a).1 ha, co b, (hB b).1 hb, ?_⟩
    rw [map_add (f := _), map_smul, hc]

end Gen

end GlobalTheory.Mem.Col2.MemLat



theorem GlobalTheory.Mem.Col2.TC.memLatAt_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (O : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).mem u).C), (∀ i c, (O.lat i c).1 = ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) → MemLatAt O (X.piT u) := by
  intro B X I hI hP l Z u O hlat
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  intro i hi
  obtain ⟨hg, hl0, hL⟩ := hsp i hi
  have hL' := (hL u I.mu0).1
  set co := GlobalTheory.Mem.Col2.Crd.co ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) with hco
  have hiso := GlobalTheory.Mem.Col2.MemLat.std_of_gram _ _ hg
  refine ⟨co, hiso, ?_, ?_⟩
  · intro y
    rw [O.lattice_integral_coordinates]
    have h1 : co y ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ y ∈ ((I.rec7 l Z).sp.X i).L0 :=
      ⟨fun ⟨z, hz, e⟩ => co.injective e ▸ hz, fun h => ⟨y, h, rfl⟩⟩
    rw [← h1, hl0]
    refine forall_congr' fun k => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r
  · intro c y
    rw [hlat i c]
    have hsep := sepElt_of_ok l.pr u
    have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
      have := hsep.conj P
      rwa [cO_cO] at this
    have hLm : ((I.rec7 l Z).clsLat u i c).map ((co : ((I.rec7 l Z).sp.X i).V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) =
        (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hL' c
    refine (GlobalTheory.Mem.Col2.MemLat.companion_crd _ co hiso _ (((I.stp u I.mu0 i).rep c).1.1.deco).1 (((I.stp u I.mu0 i).rep c).1.1.deco).2
      hLm ((B.primes X).piT u) hmem (l.pr.piT_cop u) y).trans ?_
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ 𝒮 : Set (GA D V → ℂ), (∀ φ ∈ 𝒮, Continuous φ) → (∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt V τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) → ∀ φ ∈ 𝒮, φ ∈ SmFun θ V := by
  first | exact @GlobalTheory.Mem.DerClosed.mem_smFun_of_closed | exact GlobalTheory.Mem.DerClosed.mem_smFun_of_closed | (intros; apply GlobalTheory.Mem.DerClosed.mem_smFun_of_closed <;> assumption)
end
