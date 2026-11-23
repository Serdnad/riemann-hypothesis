module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.EmbBij
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.FormEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.JointNe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.TprodNe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GRPFockOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle074
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle082
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle095
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
noncomputable section
namespace GlobalTheory.WeilContF
end GlobalTheory.WeilContF
namespace GlobalTheory.WeilContF
theorem exists_local_finite_parts_F_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := _root_.GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ co
    hco om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar F B.ψ hB.std.1 κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage F E σ nT nS JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := GlobalTheory.T.isCompact_annihilator_openSubgroup_finiteAdeles F B.ψ hB.std κ L₂' hL₂'
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition F κ L₁' hL₁' hL₁c _ hK
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', schr B.ψ (GlobalTheory.WeilCont.adeleJoin F 0 x,
      GlobalTheory.WeilCont.adeleJoin F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hNL p hp x hx y₁ hy₁
    have := impl p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y')) Φ hΦ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy'] at this
    change co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
      (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y₁) at he
    rw [he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      GlobalTheory.WeilContF.dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this
end GlobalTheory.WeilContF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weil_pair_local_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @_root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k | exact _root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k | (intros; apply _root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.weil_pair_global_intertwiner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  first | exact @_root_.GlobalTheory.DblTargetRestrictCore.restrict_core_k | exact _root_.GlobalTheory.DblTargetRestrictCore.restrict_core_k | (intros; apply _root_.GlobalTheory.DblTargetRestrictCore.restrict_core_k <;> assumption)
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP
private theorem rightSub_one_pk {n d : ℕ} : (rightSub 1 : PP n d →ₐ[ℂ] PP n d) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun l => ?_
  rcases l with ⟨b | b, c | c⟩
  · simp [rightSub, xv, Matrix.one_apply]
  · exact c.elim0
  · exact b.elim0
  · exact b.elim0
private theorem polyAction_one {n d : ℕ} (c : ℤ) : (act2 c (1 : GL (Fin d) ℂ) : Module.End ℂ (PP n d)) = 1 := by
  refine LinearMap.ext fun f => ?_
  simp [act2, detPow, rightSub_one_pk]
theorem UpperTheory.TP.realPair_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.RealPair_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he' hnd δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨Φ, a, b, hinj, hran, ha, hb, h1, h2⟩ :=
    _root_.UpperTheory.TP.RP.fockOf_k T E B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW
  have hμ : ∀ w, ∃ μ : Fin n → ℕ, ∀ k, (μ k : ℤ) + a w = (lam w).w k := fun w =>
    ⟨fun k => ((lam w).w k - a w).toNat, fun k => by
      have h3 := hdom w k
      have h4 := ha w
      rw [Int.toNat_of_nonneg (by omega)]
      omega⟩
  choose μ hμ using hμ
  have hanti : ∀ w, Antitone (μ w) := fun w i j hij => by
    have h3 := (lam w).anti hij
    have h4 := hμ w i
    have h5 := hμ w j
    omega
  choose i₁ hi₁ x₁ hx₁ using fun w => exists_act1_equivariant_nablaSq_map_hitting_joint hnd (lam w) (a w) (μ w) (hμ w)
  obtain ⟨ρ, j, hfd, hirr, hρ, hjinj, hjU, hj⟩ :=
    formEx E n hn _ (fun w => (B.emb w).1) (embBij E B) lam U hU hwt
  let J : ∀ _ : InfinitePlace (maximalRealSubfield E), PP n d := fun w => joint hnd (μ w)
  have hJ : ∀ w, J w ≠ 0 := fun w => jointNe hnd (μ w) (hanti w)
  have hx0 : ∀ w, x₁ w ≠ 0 := fun w h => hJ w (by show joint hnd (μ w) = 0; rw [← hx₁ w, h, map_zero])
  let T₀ : Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.tprod ℂ J
  have hT₀ : T₀ ≠ 0 := tprodNe J hJ
  let iV : (⨂[ℂ] w, nablaSq ℂ n (lam w)) →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.map i₁
  have hiV : iV (PiTensorProduct.tprod ℂ x₁) = T₀ := by
    simp only [iV, T₀, PiTensorProduct.map_tprod, hx₁, J]
  have hmem : ∀ T, Φ T ∈ M.Pol B.ψ B.emb := fun T => hran ▸ LinearMap.mem_range_self Φ T
  have hS : UpperTheory.TP.SameType om e U (Φ T₀) (j (PiTensorProduct.tprod ℂ x₁)) := by
    refine ⟨_, _, _, hfd, ρ, Φ ∘ₗ iV, j, PiTensorProduct.tprod ℂ x₁, hirr, ?_, rfl, hjU, fun k x => ?_, hj⟩
    · simp only [LinearMap.comp_apply, hiV]
    · have e1 : PiTensorProduct.map (fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) (iV x) =
          iV (ρ k x) := by
        rw [hρ k]
        have e2 : (PiTensorProduct.map fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) ∘ₗ iV =
            iV ∘ₗ PiTensorProduct.map fun w => GlobalTheory.Branching.sqRep ℂ n (lam w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) := by
          simp only [iV, ← PiTensorProduct.map_comp]
          congr 1
          funext w
          exact LinearMap.ext fun y => (hi₁ w _ y).symm
        exact LinearMap.congr_fun e2 x
      have := h1 k.1 k.2 (iV x)
      rw [e1] at this
      exact this
  refine ⟨Φ T₀, hmem _, fun h => hT₀ (hinj (h.trans (map_zero Φ).symm)), j (PiTensorProduct.tprod ℂ x₁), hjU _,
    fun h => tprodNe x₁ hx0 (hjinj (h.trans (map_zero j).symm)), hS, fun w => ?_⟩
  let lam' : DomWeight d := ⟨fun k => (if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w, fun p q hpq => by
    have hle : (p : ℕ) ≤ q := hpq
    dsimp only
    by_cases h3 : (q : ℕ) < n
    · have h4 : (p : ℕ) < n := by omega
      rw [dite_eq_left h3, dite_eq_left h4]
      have := hanti w (show (⟨p, h4⟩ : Fin n) ≤ ⟨q, h3⟩ from hle)
      omega
    · rw [dite_eq_right h3]
      split_ifs <;> omega⟩
  refine ⟨lam', fun k => ?_, GlobalTheory.DefU.isIrreducible_sqRep d lam', ?_⟩
  · have h3 := ha w
    have h4 := hb w
    show 2 * ((if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w) = _
    split_ifs with hk
    · have h5 := hμ w ⟨k, hk⟩
      omega
    · omega
  obtain ⟨i₂, hi₂, x₂, hx₂⟩ := exists_act2_equivariant_nablaSq_map_hitting_joint hnd lam' (b w) (μ w) (fun k => rfl)
  let up : PP n d →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := (PiTensorProduct.tprod ℂ).toLinearMap J w
  have hup : ∀ y, up y = PiTensorProduct.tprod ℂ (Function.update J w y) := fun y => rfl
  refine ⟨Φ ∘ₗ up ∘ₗ i₂, fun x => hmem _, ⟨x₂, ?_⟩, fun k hk x => ?_⟩
  · simp only [LinearMap.comp_apply, hx₂, hup]
    congr 2
    exact Function.update_eq_self_iff.2 rfl
  · have e1 : PiTensorProduct.map (fun w' => (act2 (b w') (GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k) : Module.End ℂ (PP n d))) (up (i₂ x)) =
        up (i₂ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x)) := by
      rw [hi₂, hup, hup, PiTensorProduct.map_tprod]
      congr 1
      funext w'
      by_cases hw' : w' = w
      · subst hw'
        simp
      · rw [Function.update_of_ne hw', Function.update_of_ne hw']
        have h3 := (Subgroup.mem_inf.1 hk).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 (B.emb w').1
        rw [Subgroup.mem_iInf] at h4
        have h5 : GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k = 1 := h4 fun h6 => hw' ((embBij E B).1 h6)
        rw [h5, polyAction_one]
        rfl
    have := h2 k (Subgroup.mem_inf.1 hk).1 (up (i₂ x))
    rw [e1] at this
    exact this
end
end
end

section



section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Act
theorem ctSplit_of_k : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k := fun _ _ =>
  _root_.PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_parts_k _root_.PositivityTheory.SiegelWeilFormula.Act.indepDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.cptDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k _root_.PositivityTheory.SiegelWeilFormula.Act.firstEq_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secLaw_of_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secUnf_of_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k))
end PositivityTheory.SiegelWeilFormula.Act
end
end
end
