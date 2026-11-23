module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem isDatum_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), IsDatum M ψ crd 0 0 ∧ ∀ (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ) (c : ℂ), IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + c • Φ') (f + c • f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd
  have hn : ∀ x, ‖ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  refine ⟨⟨Submodule.zero_mem _, fun u => ?_⟩, fun Φ Φ' f f' c h h' =>
    ⟨Submodule.add_mem _ h.1 (Submodule.smul_mem _ c h'.1), fun u => ?_⟩⟩
  · have e : M.co.rho ψ u (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := funext fun x => by
      simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    rw [e]
    simp [GlobalTheory.WeilM.thetaSum]
  · have s1 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h.1).1 (M.co.e u)
    have s2 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ' (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h'.1).1 (M.co.e u)
    have e : M.co.rho ψ u (Φ + c • Φ') = M.co.rho ψ u Φ + c • M.co.rho ψ u Φ' := funext fun x => by
      simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← h.2 u, ← h'.2 u]
    unfold GlobalTheory.WeilM.thetaSum
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [s1.tsum_add (s2.mul_left c), tsum_mul_left]

end GlobalTheory.SquareAgree
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_rational_darboux_orientedPair_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  first | exact @GlobalTheory.SquareAgree.exists_darboux_transport | exact GlobalTheory.SquareAgree.exists_darboux_transport | (intros; apply GlobalTheory.SquareAgree.exists_darboux_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open GlobalTheory.SmallThetaModules in
theorem exists_algD_not_polMatch_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf h
  classical
  let s : ∀ v, Rf.Pi v := fun v => Rf.p' v (G.M'.vac v)
  have hsph : ∀ v ∉ X.T, Rf.p v (G.M.vac v) = s v := fun v hv => (h.fin.sph v hv).1
  have hs0 : ∀ v ∉ X.T, s v ≠ 0 := fun v hv => by
    rw [← hsph v hv]; exact (h.fin.sph v hv).2
  have hXT : (X.T : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))).Finite := X.T.finite_toSet
  obtain ⟨q, hq⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V G.W G.M B.ψ h.triple.geo.hM R.Pi R.p Rf.Pi Rf.p s
    (Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hsph v hn)))
  obtain ⟨q', hq'⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V' G.W G.M' B.ψ h.triple.geo.hM' R.Pi R.p' Rf.Pi Rf.p' s
    (Filter.Eventually.of_forall fun v => rfl)
  haveI := h.real.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
  have hx' : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [h.real.quot'.onto]; trivial
  obtain ⟨f, hf, hfx⟩ := hx'
  have hloc : ∀ v, ∃ φv, φv ∈ GlobalTheory.WeilM.SB _ ∧ Rf.p' v φv ≠ 0 ∧ (v ∉ X.T → φv = G.M'.vac v) := by
    intro v
    by_cases hv : v ∈ X.T
    · haveI := h.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [h.fin.onto' v]; trivial
      obtain ⟨φv, h1, h2⟩ := hy'
      exact ⟨φv, h1, h2 ▸ hy, fun hn => absurd hv hn⟩
    · exact ⟨G.M'.vac v, (h.triple.geo.hM'.vac v).1, hs0 v hv, fun _ => rfl⟩
  choose φ hφSB hφ0 hφvac using hloc
  have hφev : ∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v :=
    Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hφvac v hn))
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD G.M' B.ψ B.emb :=
    Submodule.subset_span ⟨f, φ, hf, hφSB, hφev, rfl⟩
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  choose l hl using fun v => Module.Projective.exists_dual_eq_one ℂ (hφ0 v)
  have hls : ∀ v ∉ X.T, l v (s v) = 1 := fun v hv => by
    have := hl v
    rwa [hφvac v hv] at this
  have hadm : {v | l v (s v) ≠ 1}.Finite := hXT.subset fun v hv => by by_contra hn; exact hv (hls v hn)
  obtain ⟨Λ, hΛ⟩ := pureT_sep s (fun v => l v) hadm
  let LL : R.Pi ⊗[ℂ] RTens s →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ Λ)
  have hLL : ∀ x y, LL (x ⊗ₜ y) = l₀ x * Λ y := fun x y => by simp [LL]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, hΦ, ?_⟩
  rintro ⟨T, hT, m, m', fs, φs, fs', φs', hfam, hfam', h0, hΦe, htens⟩
  let LT : (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := PiTensorProduct.dualDistrib (⨂ₜ[ℂ] v : T, l v)
  let Ltot : R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ LT)
  have hLtot : ∀ x y, Ltot (x ⊗ₜ y) = l₀ x * LT y := fun x y => by simp [Ltot]
  have key : ∀ g : ∀ v, Rf.Pi v, (∀ v ∉ T, g v = s v) →
      Λ (pureT s g) = LT (PiTensorProduct.tprod ℂ fun v : T => g v) := by
    intro g hg
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s g := T.finite_toSet.subset fun v hv => by by_contra hn; exact hv (hg v hn)
    rw [hΛ g hr]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv => by
      by_contra hn
      exact hv (by show l v (g v) = 1; rw [hg v hn]; exact hls v fun h' => hn (hT h')))]
    simp only [LT, PiTensorProduct.dualDistrib_apply]
    exact (Finset.prod_coe_sort T fun v => l v (g v)).symm
  have hP : ∀ i, LL (q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs i) (φs i))) =
      Ltot (R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) := by
    intro i
    have ev : ∀ᶠ v in Filter.cofinite, φs i v = G.M.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam i).2.2 v hn))
    rw [hq _ _ (hfam i).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam i).2.2 v hv]; exact hsph v fun h' => hv (hT h')
  have hP' : ∀ j, LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs' j) (φs' j))) =
      Ltot (R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    intro j
    have ev : ∀ᶠ v in Filter.cofinite, φs' j v = G.M'.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam' j).2.2 v hn))
    rw [hq' _ _ (hfam' j).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam' j).2.2 v hv]
  have h1 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = 1 := by
    rw [hq' _ _ hφSB hφev, hLL, hfx, hl₀, one_mul]
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => Rf.p' v (φ v)) :=
      hXT.subset fun v hv => by by_contra hn; exact hv (congrArg (Rf.p' v) (hφvac v hn))
    rw [hΛ _ hr]
    exact finprod_eq_one_of_forall_eq_one fun v => hl v
  have h2 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      Ltot (∑ j, R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by

    rw [hΦe, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hP' j
  have h3 : Ltot (∑ i, R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) = 0 := by

    rw [map_sum, ← Finset.sum_congr rfl fun i _ => hP i, ← map_sum, ← map_sum, ← h0, map_zero, map_zero]
  rw [htens, ← h2, h1] at h3
  exact one_ne_zero h3

end GlobalTheory.SquareAgree
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.InfKill.smul_mat_kapX_sub_one | exact GlobalTheory.InfKill.smul_mat_kapX_sub_one | (intros; apply GlobalTheory.InfKill.smul_mat_kapX_sub_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

theorem _root_.GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  first | exact @GlobalTheory.SquareAgree.pureA_mem_algD | exact GlobalTheory.SquareAgree.pureA_mem_algD | (intros; apply GlobalTheory.SquareAgree.pureA_mem_algD <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.transposeGramUnitary_surjective_finitePlaceSupported : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v), ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  first | exact @GlobalTheory.SquareAgree.KapOnto.kapX_onto | exact GlobalTheory.SquareAgree.KapOnto.kapX_onto | (intros; apply GlobalTheory.SquareAgree.KapOnto.kapX_onto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.KapXLine.exists_line | exact GlobalTheory.KapXLine.exists_line | (intros; apply GlobalTheory.KapXLine.exists_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_lieGenerator_of_oneParameterSubgroup_realPlace : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.LineAtPlace.exists_oneP | exact GlobalTheory.LineAtPlace.exists_oneP | (intros; apply GlobalTheory.LineAtPlace.exists_oneP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.finprod_finiteHeight_transposeGramUnitary_le : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤ C * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  first | exact @GlobalTheory.SquareAgree.finprod_htFin_kapX_le | exact GlobalTheory.SquareAgree.finprod_htFin_kapX_le | (intros; apply GlobalTheory.SquareAgree.finprod_htFin_kapX_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

theorem _root_.GlobalTheory.T.rank_algebraicData_schrodingerModel_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    Module.rank ℂ (M.Pol ψ emb) ≤ Cardinal.aleph0 →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Module.rank ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ≤ Cardinal.aleph0) →
    Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.AlgCountDim.rank_algD_le_aleph0 | exact GlobalTheory.AlgCountDim.rank_algD_le_aleph0 | (intros; apply GlobalTheory.AlgCountDim.rank_algD_le_aleph0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImage

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_add {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul {κ : Type} [Fintype κ] (c : ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_zero {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem map_eq {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (Th : ((Fin n × Fin d → AF F) → ℂ) → Q)
    (T : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Q) (Alg : Submodule ℂ Q)
    (hsub : GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ = Th Φ)
    (hvac : ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      M.IsGauss ψ τ f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ Alg)
    (hder : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ)
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      f ∈ M.Pol ψ τ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ →
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg → Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) ∈ Alg)
    (hrev : Alg ≤ (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T) :
    (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T = Alg := by
  refine le_antisymm ?_ hrev
  have hmem : ∀ f ∈ M.Pol ψ τ, ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := fun f hf φ h1 h2 =>
    hT _ (hsub (Submodule.subset_span ⟨f, φ, hf, h1, h2, rfl⟩))
  have hG : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hC : ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → ∀ f ∈ M.Pol ψ τ,
      ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ :=
    fun u hu f hf f₁ hA => Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ hA
  let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧ ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg}
      add_mem' := fun {f g} hf hg => ⟨(M.Pol ψ τ).add_mem hf.1 hg.1, fun φ h1 h2 => by
        rw [pure_add, map_add (f := _)]; exact Alg.add_mem (hf.2 φ h1 h2) (hg.2 φ h1 h2)⟩
      zero_mem' := ⟨(M.Pol ψ τ).zero_mem, fun φ _ _ => by rw [pure_zero, map_zero]; exact Alg.zero_mem⟩
      smul_mem' := fun c f hf => ⟨(M.Pol ψ τ).smul_mem c hf.1, fun φ h1 h2 => by
        rw [pure_smul, map_smul]; exact Alg.smul_mem c (hf.2 φ h1 h2)⟩ }
  have hPN : M.Pol ψ τ ≤ N := sInf_le ⟨fun f₀ h => ⟨hG f₀ h, fun φ h1 h2 => by
      rw [hmem f₀ (hG f₀ h) φ h1 h2]; exact hvac f₀ φ h h1 h2⟩,
    fun u hu f hf f₁ hA => ⟨hC u hu f hf.1 f₁ hA, fun φ h1 h2 => by
      rw [hmem f₁ (hC u hu f hf.1 f₁ hA) φ h1 h2]
      exact hder f φ u f₁ hf.1 hu hA h1 h2 (by rw [← hmem f hf.1 φ h1 h2]; exact hf.2 φ h1 h2)⟩⟩
  rw [Submodule.map_le_iff_le_comap]
  unfold GlobalTheory.TripleAssembly.darbAlg
  rw [Submodule.span_le]
  rintro Φ ⟨f, φ, hf, h1, h2, rfl⟩
  exact (hPN hf).2 φ h1 h2

end Generic

end GlobalTheory.DarbImage

namespace GlobalTheory.DarbImage

end GlobalTheory.DarbImage

end
end
