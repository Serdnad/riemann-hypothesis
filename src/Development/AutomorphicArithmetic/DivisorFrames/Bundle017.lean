module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle014
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveSemilinearNablaTWtOpEquivariant
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle012
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177

@[expose] public section

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem core {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] {n : ℕ} (F : Frame l ι n) {H : Type} [Group H]
    (e : F.G ≃* H) (io : PadicAlgCl l ≃+* ℂ) (A : H →* (ι → GL (Fin n) (PadicAlgCl l))) (bs : ι → GL (Fin n) (PadicAlgCl l))
    (sh : ι → ℤ) (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hf : F.IsEig mu θ) :
    ∃ Fm : H → NablaT ℂ n mu, Fm ≠ 0 ∧
      (∀ γ, e.symm γ ∈ F.Γ → ∀ g,
        Fm (γ * g) = wtOp ℂ n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (A γ τ)) (Fm g)) ∧
      (∀ κ : F.K, (∀ τ, Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) = (bs τ)⁻¹ * A (e κ) τ * bs τ) → ∀ c : ℂ,
        io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * c = 1 → ∀ g, Fm (g * e κ) = c • Fm g) ∧
      ∀ i (S : Finset H), (∀ g, g ∈ F.tr i ↔ e g ∈ S) → F.cst i = 1 → (∀ a ∈ S, A a = 1) → ∀ g,
        ∑ a ∈ S, Fm (g * a) = io (θ i) • Fm g := by
  classical
  obtain ⟨f, hf0, ⟨hf1, hf2⟩, hf3⟩ := hf
  obtain ⟨Φ, hΦ, hΦs, hΦw⟩ := UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant _ _ io n ι mu sh
  refine ⟨fun g => Φ (wtOp _ n mu sh (A g * bs) (f (e.symm g))), fun h => hf0 ?_, fun γ hγ g => ?_, fun κ hκ c hc g => ?_,
    fun i S hS hc hA g => ?_⟩
  · funext x
    have h1 : Φ (wtOp _ n mu sh (A (e x) * bs) (f (e.symm (e x)))) = 0 := congrFun h (e x)
    rw [e.symm_apply_apply, ← Φ.map_zero] at h1
    have h2 := congrArg (wtOp _ n mu sh (A (e x) * bs)⁻¹) (hΦ h1)
    rw [← Module.End.mul_apply, ← wtOp_mul, inv_mul_cancel, wtOp_one, map_zero] at h2
    exact h2
  · show Φ _ = wtOp _ _ _ _ _ (Φ _)
    rw [← hΦw, map_mul, map_mul, hf1 _ hγ, mul_assoc, wtOp_mul, Module.End.mul_apply]
  · show Φ _ = c • Φ _
    have hk : A (g * e κ) * bs = (A g * bs) * fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) := by
      funext τ
      simp only [Pi.mul_apply, map_mul, hκ]
      group
    rw [hk, map_mul, e.symm_apply_apply, wtOp_mul, Module.End.mul_apply, ← hf2 κ (e.symm g),
      wtOp_apply _ _ _ _ (fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)), LinearMap.map_smul, LinearMap.map_smul, hΦs, hΦs, smul_smul]
    congr 1
    have hd : ∀ τ, ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)) : (PadicAlgCl l)ˣ) :
        PadicAlgCl l) = F.emb (F.kap κ τ).val.det := fun τ => by
      simp [RingHom.map_det]
    simp only [zpow_neg, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hd]
    rw [map_mul] at hc
    rw [map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hc]
    ring
  · have h1 : ∑ a ∈ S, f (e.symm g * e.symm a) = ∑ s ∈ F.tr i, f (e.symm g * s) :=
      (Finset.sum_equiv e.toEquiv hS fun s _ => by simp).symm
    have h2 := hf3 i (e.symm g)
    rw [hc, map_one, one_smul, ← h1] at h2
    show ∑ a ∈ S, Φ _ = _ • Φ _

    rw [← hΦs, ← LinearMap.map_smul, ← h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, map_mul, hA a ha, mul_one]


theorem UpperTheory.exists_nonzero_vectorValued_eigenform_unitary :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime]
        (F : Frame l D.what₂.Tau (Vc D j).rank) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
        (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
        (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l), F.IsEig mu θ →
        ∃ Fm : Bridge.Gf (Vc D j) → NablaT ℂ (Vc D j).rank mu, Fm ≠ 0 ∧
          (∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (γ₀ : GL (Fin (Vc D j).rank) D.host.E),
            Formalism.L2.Theta.matHom (Vc D j) γ = Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.incA D) γ₀ → ∀ g,
            Fm (Bridge.ratF (Vc D j) γ * g) = wtOp ℂ (Vc D j).rank mu T.sh
              (fun τ => Matrix.GeneralLinearGroup.map (T.io.toRingHom.comp (inc τ)) γ₀) (Fm g)) ∧
          (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) ∧
          ∀ i, (∀ a ∈ hkA p j t (ix i), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t (ix i).1) a) → ∀ g,
            ∑ a ∈ hkA p j t (ix i), Fm (g * a) = T.io (θ i) • Fm g := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t l _ F e0 ix inc T mu θ hf
  obtain ⟨A, hA⟩ : ∃ A : Bridge.Gf (Vc D j) →* (D.what₂.Tau → GL (Fin (Vc D j).rank) (PadicAlgCl l)),
      ∀ g τ, (A g τ).val = (matOf j g).map (T.ev τ) :=
    ⟨MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (T.ev τ)).comp (Bridge.Gf (Vc D j)).subtype, fun _ _ => rfl⟩
  obtain ⟨Fm, h0, h1, h2, h3⟩ := core F T.e T.io A T.bs T.sh mu θ hf
  refine ⟨Fm, h0, fun γ γ₀ hγ g => ?_, fun κ g => ?_, fun i hi g => ?_⟩
  · rw [h1 _ ((T.rat _).2 ⟨γ, (T.e.apply_symm_apply _).symm⟩)]
    congr 2
    funext τ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h4 : (Formalism.L2.Theta.matHom (Vc D j) γ).val a b = Formalism.L2.Theta.incA D (γ₀.val a b) := by rw [hγ]; rfl
    have h5 : matOf j (Bridge.ratF (Vc D j) γ) a b = 1 ⊗ₜ[D.host.F] γ₀.val a b :=
      congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) h4
    show T.io ((A _ τ).val a b) = T.io (inc τ (γ₀.val a b))
    rw [hA, Matrix.map_apply, h5, T.ev_rat]
  · have hrk : (T.rk : Fin (Vc D j).rank → Fin (Vc D j).rank) = id := by
      rw [Subsingleton.elim T.rk (OrderIso.refl _)]; rfl
    have hk : ∀ (k : F.K) τ, Matrix.GeneralLinearGroup.map F.emb (F.kap k τ) = (T.bs τ)⁻¹ * A (T.e k) τ * T.bs τ := by
      intro k τ
      have h := T.kap k τ
      rw [hrk, Matrix.submatrix_id_id, ← hA, ← Units.val_mul, ← Units.val_mul] at h
      exact Units.ext h
    obtain ⟨κ, hκ⟩ := κ
    obtain ⟨k, rfl⟩ := T.e.surjective κ
    obtain ⟨k', rfl⟩ : ∃ k' : F.K, (k' : F.G) = k := ⟨⟨k, (T.lev k).2 hκ⟩, rfl⟩
    exact h2 k' (hk k') _ (T.chi k' hκ) g
  · refine h3 i _ (T.tr i) (T.cst i) (fun a ha => ?_) g
    funext τ
    exact Units.ext ((hA a τ).trans
      (UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd D (Vc D j) l (T.ev τ) (T.ev_int τ) _ ((T.ix_range _).1 ⟨i, rfl⟩).2.2 a (hi a ha)))
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem exists_Q {ι : Type} [Fintype ι] [DecidableEq ι] {V U : ι → Type} [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)] [∀ τ, FiniteDimensional ℂ (V τ)]
    (P : ∀ τ, V τ →ₗ[ℂ] U τ →ₗ[ℂ] ℂ) (hP : ∀ τ, Function.Bijective (P τ).flip) :
    ∃ F : (Π τ, V τ) →ₘₗ[ℂ] (PiTensorProduct ℂ U →ₗ[ℂ] ℂ), (∀ u, (∀ v, F v u = 0) → u = 0) ∧
      ∀ v u, F v (PiTensorProduct.tprod ℂ u) = ∏ τ, P τ (v τ) (u τ) := by
  let e : ∀ τ, U τ ≃ₗ[ℂ] Module.Dual ℂ (V τ) := fun τ => LinearEquiv.ofBijective (P τ).flip (hP τ)
  let Q : PiTensorProduct ℂ U ≃ₗ[ℂ] Module.Dual ℂ (PiTensorProduct ℂ V) :=
    (PiTensorProduct.congr e).trans PiTensorProduct.dualDistribEquiv
  refine ⟨(LinearMap.flip Q.toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ), fun u hu => ?_, fun v u => ?_⟩
  · apply Q.injective
    rw [map_zero]
    apply PiTensorProduct.ext
    ext v
    exact hu v
  · change PiTensorProduct.dualDistrib (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ u))
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.congr_tprod, PiTensorProduct.dualDistrib_apply]
    rfl

open Formalism.L2.DIV GlobalTheory.CoefIrred in
theorem UpperTheory.exists_invariant_nondegenerate_pairing_weightRep_nablaT :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n),
        (∀ τ (a : Fin n), (lam τ).w a = (mu τ a : ℤ) + sh τ) →
        ∃ P : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, (∀ v, P v u = 0) → u = 0) ∧
          ∀ (g : ι → GL (Fin n) ℂ) v u, P (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = P v u := by
  intro n ι _ _ mu sh lam hl
  choose P1 hb hi using fun τ =>
    UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hl τ a)
  obtain ⟨F, hF0, hF⟩ := exists_Q P1 hb
  have hUniversal : ∃! P : VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ,
      ∀ w, P (tenMul lam w) = F w := by
    have hBasis : ∀ i, bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
      intro i
      apply Subtype.ext
      rw [bVV_coe, tenMul_coe, bVVfun]
      simp only [ssBasis_coe]
    let p := (bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))
    refine ⟨p, ?_, ?_⟩
    · have hComp : p.compMultilinearMap (tenMul lam) = F := by
        apply Module.Basis.ext_multilinear (fun τ => ssBasis ℂ (lam τ))
        intro i
        simp only [LinearMap.compMultilinearMap_apply, ← hBasis, p, Module.Basis.constr_basis]
      intro w
      exact congrArg (fun m => m w) hComp
    · intro q hq
      apply (bVV ℂ lam).ext
      intro i
      simp only [p, Module.Basis.constr_basis]
      rw [hBasis, hq]
  obtain ⟨P, hP, hUnique⟩ := hUniversal
  refine ⟨P, fun u hu => hF0 u fun v => by rw [← hP]; exact hu _, fun g v u => ?_⟩
  have key : (P ∘ₗ Formalism.L2.DIV.rhoK lam g).compl₂ (wtOp ℂ n mu sh g) = P := by
    refine hUnique _ (fun w => ?_)
    apply PiTensorProduct.ext
    ext x
    change P (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam w))
      (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ x)) = F w (PiTensorProduct.tprod ℂ x)
    rw [rhoK_tenMul, hP, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hF, hF]
    simp only [hi]
    rw [Finset.prod_mul_distrib, smul_eq_mul, ← mul_assoc, ← Units.coe_prod, ← Units.val_mul,
      ← Finset.prod_mul_distrib]
    simp
  exact LinearMap.congr_fun (LinearMap.congr_fun key v) u
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_smul' {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (a : AF D.host.F)
    (x : Mx D d m) : ptO G e (a • x) = a • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.smul_mul, transpose_smul]
  rfl

private theorem ptO_zero' {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    ptO G e (0 : Mx D d m) = 0 := by
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.zero_mul]
  rfl

private theorem realAd_one_smul {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {u : U}
    (hu : At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F 1 • u = u := by
  have h := hu (1 - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F 1) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (1 : ℝ))) = 0
    rw [map_sub, RingEquiv.apply_symm_apply, map_one, map_one, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm


theorem UpperTheory.exists_polynomial_of_isFinF_thetaLift_pureTensor :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (θ : InfFam D), IsInfFam θ → ∀ (A : Fr S) (B : Fr X), IsCart ε A B e Bs Vs Ws →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d))
          (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → g ≠ 0 → (∀ v, φ v ≠ 0) →
        IsFinF ψ θ ε A B (thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) →
        ∀ g₁ ∈ M.Pol Bs.ψ Bs.emb, ∃ P : PolF D X.rank S.rank,
          fockF ψ θ ε A B (thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P =
            thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) := by
  intro D ψ ε S X d e Bs Vs Ws M hP θ hθ A B hc g φ hSB hev g0 hφ0 hv
  obtain ⟨-, hH, tadd, tsm, tinj, -⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hBs, hψe, hJ, hJW, ⟨r, s, hV⟩, ⟨r', s', hW⟩, hM⟩ := hP
  subst hψe
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
    (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hm : ∀ f : SInf D.host.F (Fin S.rank × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA D.host.F _ := fun f =>
    GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SInf D.host.F (Fin S.rank × Fin d) →ₗ[ℂ] (WO (sgn ε S) X → ℂ),
      ∀ f, Θ f = thO M Bs.ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) :=
    ⟨{ toFun := fun f => thO M Bs.ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)
       map_add' := fun f f' => by
         rw [← tadd _ (hm f) _ (hm f')]
         exact congrArg _ (funext fun x => add_mul _ _ _)
       map_smul' := fun c f => by
         rw [RingHom.id_apply, ← tsm]
         exact congrArg _ (funext fun x => mul_assoc _ _ _) }, fun _ => rfl⟩
  have hi : ∀ f, Θ f = 0 → f = 0 := fun f h => by
    by_contra hf
    refine GlobalTheory.EvNonzero.pure_ne_zero f hf φ hφ0 hstd (tinj _ (hm f) _ (zero_mem _) ?_)
    rw [← hΘ, h]
    simpa only [zero_smul] using (tsm 0 0).symm
  obtain ⟨Dr, hD1, hD2, hD3⟩ := GlobalTheory.RealDict.FockMap.exists_der M hBs.std
  obtain ⟨dir, hdir⟩ : ∃ dir : D.what₂.Tau → Matrix (Fin X.rank) (Fin S.rank) ℂ → Matrix (Fin S.rank) (Fin d) (AE D),
      ∀ t z, dir t z = ptO (sgn ε S).gram e (lineAt θ t z 1) := ⟨_, fun _ _ => rfl⟩
  have hat : ∀ t z, At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (dir t z) := fun t z a ha => by
    rw [hdir, ← ptO_smul', (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ t z).2 a ha, ptO_zero']
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO Bs.ψ (sgn ε S) X) θ t z (Θ f) = Θ (Dr (dir t z) f) := by
    intro t z f
    have hl := (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ t z).1
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f
        (fun x : Fin S.rank × Fin d → AF D.host.F => ∏ᶠ v, φ v fun i => evFin D.host.F v (x i)) :=
      GlobalTheory.RealDict.FockMap.rest_fin f
        (g := fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (y i))
        ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
    funext x
    have := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho M.co Bs.ψ inferInstance hψ.1 (dir t z) _ (hm f) _ (hm (Dr (dir t z) f))
      (hD1 _ (hat t z) f _ hrest) (ptO (sgn ε S).gram e x)
    rw [hΘ (Dr _ _)]
    refine Eq.trans ?_ this.deriv
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext a
    rw [hΘ, ← hH, hl a, ptO_smul', ← hdir]
    rfl
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hg : (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) =
      (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul]; rfl
    · simp only [if_true, neg_smul, one_smul]; exact neg_gram S
  obtain ⟨cS, hcS, hcS'⟩ : ∃ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D))) ∧ ∀ x, cS.symm x = ptO (sgn ε S).gram e x :=
    ⟨GlobalTheory.FockThetaOnto.crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e,
      fun u => by rw [← hg]; rfl, fun _ => rfl⟩
  have hsum : ∀ u, At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f, Dr u f = ∑ t, Dr (dir t (compAt θ t (cS u))) f := by
    intro u hu f
    have h : At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (show Mx D X.rank S.rank from cS u) := fun a ha => by
      have h0 : a • uᵀ.submatrix e.symm id = 0 := congrArg (fun y => yᵀ.submatrix e.symm id) (hu a ha)
      show a • (show Mx D X.rank S.rank from cS u) = 0
      rw [hcS, ← Matrix.smul_mul, h0, Matrix.zero_mul]
    have h1 := congrArg cS.symm (GlobalTheory.RealDict.FockMap.eq_sum_lineAt hθ h)
    have h2 : u = ∑ t, dir t (compAt θ t (cS u)) := by
      refine ((cS.symm_apply_apply u).symm.trans h1).trans ((map_sum cS.symm _ _).trans ?_)
      exact Finset.sum_congr rfl fun t _ => (hcS' _).trans (hdir _ _).symm
    rw [← hD3 _ _ _ fun t => hat t _, ← h2]
  rw [← hΘ] at hv ⊢
  have hg₀ : ∀ t z, Dr (dir t z) g + Complex.I • Dr (dir t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g = 0 := fun t z =>
    hi _ (by rw [map_add (f := _), map_smul, ← hd, ← hd]; exact hv.2 t z)
  have hGa : M.IsGauss Bs.ψ Bs.emb g := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have k := GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e.symm Bs Vs Ws hc cS hcS u u' (fun w => by simpa using hrel w) t
    rw [GlobalTheory.VacTransfer.archLine_apply, GlobalTheory.VacTransfer.archLine_apply, realAd_one_smul hu, realAd_one_smul hu'] at k
    rw [k, eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (cS u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  intro g₁ hg₁
  rw [← hΘ]
  have hle : M.Pol Bs.ψ Bs.emb ≤ (LinearMap.range (fockF Bs.ψ θ ε A B (Θ g))).comap Θ := by
    refine sInf_le ⟨fun f hf => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M Bs.ψ Bs.emb hBs.cm hBs.std (fun w => (hV.cartan w).1)
        (fun w => (hW.cartan w).1) f g hGa g0 hf
      exact Submodule.smul_mem _ z ⟨1, GlobalTheory.LieScalar.ptF_one (frSgn ε A) B _⟩
    · rintro u hu f ⟨P, hP⟩ f₁ h1
      rw [hD2 u hu _ _ h1, hsum u hu]
      refine Submodule.sum_mem _ fun t _ => ?_
      obtain ⟨Q, hQ⟩ := GlobalTheory.RealDict.FockMap.dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (cS u)) P
      refine ⟨Q, ?_⟩
      rw [← hd, ← hP]
      exact hQ.symm
  exact hle hg₁
end
