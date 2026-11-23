module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle576
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle579
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

theorem mem_of_pure {A : Type} [AddCommGroup A] [Module ℂ A] {ι : Type} [Fintype ι] {B : ι → Type}
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (S : Submodule ℂ (A ⊗[ℂ] (⨂[ℂ] i, B i)))
    (h : ∀ x φ, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ ∈ S) : ∀ t, t ∈ S := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r φ => rw [TensorProduct.tmul_smul]; exact S.smul_mem r (h x φ)
    | add y z hy hz => rw [TensorProduct.tmul_add]; exact S.add_mem hy hz
  | add s t hs ht => exact S.add_mem hs ht

theorem mem_of_tprod {ι : Type} [Fintype ι] {B : ι → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (S : Submodule ℂ (⨂[ℂ] i, B i)) (h : ∀ φ, PiTensorProduct.tprod ℂ φ ∈ S) : ∀ y, y ∈ S := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r φ => exact S.smul_mem r (h φ)
  | add y z hy hz => exact S.add_mem hy hz

def ext (M : Model σ Y W) (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ :=
  fun v => if h : v ∈ T then ((φ ⟨v, h⟩ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v

variable (M : Model σ Y W) (T : Finset (Pl F))

theorem ext_of_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) :
    ext M T φ v.1 = (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  simp [ext, v.2]

theorem ext_of_not_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl F) (hv : v ∉ T) :
    ext M T φ v = M.vac v := by
  simp [ext, hv]

theorem ext_mem_SB {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (v : Pl F) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact (hM.vac v).1

theorem ext_vac (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = M.vac v := by
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact ext_of_not_mem M T φ v hv

theorem ext_std {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hM.std] with v h1 h2
  rw [h1, h2]

theorem ext_update [DecidableEq T] (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T)
    (z : ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ext M T (Function.update φ v z) = Function.update (ext M T φ) v.1 (z : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  funext w
  by_cases hw : w ∈ T
  · by_cases hwv : w = v.1
    · subst hwv
      rw [ext_of_mem M T _ v, Function.update_self, Function.update_self]
    · have hne : (⟨w, hw⟩ : T) ≠ v := fun e => hwv (congrArg Subtype.val e)
      rw [ext_of_mem M T _ ⟨w, hw⟩, Function.update_of_ne hwv, Function.update_of_ne hne, ext_of_mem M T _ ⟨w, hw⟩]
  · have hwv : w ≠ v.1 := fun e => hw (e ▸ v.2)
    rw [ext_of_not_mem M T _ w hw, Function.update_of_ne hwv, ext_of_not_mem M T _ w hw]

end GlobalTheory.HoweGlobal.Transfer

end

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))

theorem rest_ext {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)

theorem acts_ext [DecidableEq T] {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hM φ)) ?_
  simpa only [ext_of_mem] using h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w) (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hM φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobal.Transfer


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.VacTransfer



theorem exists_darboux_cS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ u, co.e (cS u) = M.co.e u := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hc
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D))
    (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J)
    (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  refine ⟨1, D.host.xi0 • (sgn ε S).gram⁻¹, co, one_smul _ _, fun x => ?_, hco⟩
  obtain ⟨y, z, h⟩ := hM.rat ((x * G⁻¹)ᵀ.submatrix id e.symm)
  refine ⟨y, z, Eq.trans ?_ h⟩
  rw [← hco, hc]
  congr 1
  exact (map_transpose_inv_mul (incA D) e x hdet).symm

theorem vacDatum_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  subst hψ
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  obtain ⟨ξ, JB, co, hJB, hrat, hco⟩ :=
    exists_darboux_cS D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F co Bs.ψ Φ = f := by
    funext w
    obtain ⟨u, rfl⟩ := cS.surjective w
    refine Eq.trans ?_ (hD.2 u)
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco]
  have hvac : ∀ τ z, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f =
      Complex.I • dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f := by
    intro τ z
    funext w
    have h0 := congrFun (hf.2 τ z) w
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (-Complex.I) * h0 +
      dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f w * Complex.I_sq
  refine ⟨fun _ => 1, fun u u' _ _ hrel x => ?_⟩
  have hrel' : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := fun w => by
    simpa using hrel w
  obtain ⟨hc, hc0⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u
  obtain ⟨hc', hc0'⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u'
  have key : (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u' t) f w) 0) =
      Complex.I • (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u t) f w) 0) := by
    refine (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u') hc' hc0').trans
      (Eq.trans ?_ (congrArg (Complex.I • ·) (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u) hc hc0).symm))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact (congrArg (fun z => dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f)
      (GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e Bs Vs Ws hcart cS hcS u u' hrel' τ)).trans (hvac τ _)
  rw [← hΦf] at key
  have h1 := GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv D Bs.ψ hstd (sgn ε S) X JB ξ hJB (Fin S.rank × Fin d) co hrat Φ hD.1 (archLine cS u) (archLine cS u')
    hc hc0 hc' hc0' Complex.I key x
  simpa only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, archLine_apply, hco] using h1

end GlobalTheory.VacTransfer

end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem RelV.exists_decomp_of_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hx
    refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hSB, fun v hv => ?_⟩, ?_⟩
    · by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    · simp
  | zero => exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2.1, (h i).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem RelV.pure_neg {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (-f) φ = -pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.neg_apply, Pi.neg_apply, neg_mul]

theorem polZero_relV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  classical
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ
  obtain ⟨T₀, m, f, φ, hφ, rfl⟩ := RelV.exists_decomp_of_mem_algD G.M Bs.ψ Bs.emb hΦ
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  choose ψ hψ using fun i => GlobalTheory.ThK.LocalOps.acts_exists hP v (g, 1) hg h1W (φ i v) ((hφ i).2.1 v)
  have hpv : ∀ i, Rf.p v (ψ i) = Rf.p v (φ i v) := by
    intro i
    have hmem : ψ i - φ i v ∈ augAt om v :=
      Submodule.subset_span ⟨g, hg, φ i v, (hφ i).2.1 v, ψ i, (hψ i).1, (hψ i).2, rfl⟩
    have := hM.fin.inv v hmem
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    have e0 : ∀ᶠ w in Filter.cofinite, φ i w = G.M.vac w :=
      Filter.eventually_cofinite.2 ((T₀.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw ((hφ i).2.2 w hc))
    filter_upwards [e0, hT.geo.hM.std] with w e1 e2
    rw [e1, e2]
  set T : Finset (Pl F) := insert v (Xc.T ∪ T₀) with hTdef
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ Finset.mem_insert_self _ _)
  have hT₀ : ∀ w, w ∉ T → w ∉ T₀ := fun w hw h =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  refine ⟨T, fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_left _ hw), m + m,
    Fin.append f fun i => -f i, Fin.append (fun i => Function.update (φ i) v (ψ i)) φ, fun k => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
      refine ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩
      · by_cases hw : w = v
        · subst hw; rw [Function.update_self]; exact (hψ i).1
        · rw [Function.update_of_ne hw]; exact (hφ i).2.1 w
      · rw [Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w (hT₀ w hw)
    · simp only [Fin.append_right]
      exact ⟨neg_mem (hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w (hT₀ w hw)⟩

  · rw [map_sum, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, RelV.pure_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ThK.PolMatchStep.pure_update v (om (g, 1)) (f i) (φ i) (hφ i).2.1 (hstd i) (hψ i).2
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    have e : ∀ i, (fun w : T => Rf.p w (Function.update (φ i) v (ψ i) w)) = fun w : T => Rf.p w (φ i w) := by
      intro i
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
        exact hpv i
      · simp only [Function.update_of_ne hwv]
    simp only [e, add_neg_cancel]

end GlobalTheory.PolKer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumUniq

theorem idemSum_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  intro D P e e' h h'
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ PP PP (hes PP hP) (hes' PP hP)).1 rfl

end GlobalTheory.IdemSumUniq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finite_element_conj_rowLevel_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  first | exact @GlobalTheory.SeeConj.exists_conj_level | exact GlobalTheory.SeeConj.exists_conj_level | (intros; apply GlobalTheory.SeeConj.exists_conj_level <;> assumption)
end
