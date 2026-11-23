module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.RankFibre

def stabSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem of_parts (Lirr : (GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M)) (Llaw : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)))) (Lsmooth : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ})) (Linteg : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))))) (Lker : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b))) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  intro HB k _ _ _ _ a d had ν β hνs hνu hβs hβu N hCN hNSB hNst
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  borelize k

  have hS0 : ∀ (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      Φ ∈ fullRankSB k a (a + b) → omA ν β 1 h Φ ∈ fullRankSB k a (a + b) := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]

  have hint : ∀ Φ ∈ fullRankSB k a (a + b), ∀ x : GL (Fin (a + b)) k,
      Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + b : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => Linteg k a b ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + b), ∀ Ψ ∈ fullRankSB k a (a + b),
      fibre ν β a b (Φ + Ψ) = fibre ν β a b Φ + fibre ν β a b Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      fibre ν β a b (c • Φ) = c • fibre ν β a b Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fibre ν β a b 0 = 0 := by
    funext x
    simp [fibre, omA]

  let M : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
    { carrier := {f | ∃ Ψ ∈ N, Ψ ∈ fullRankSB k a (a + b) ∧ fibre ν β a b Ψ = f}
      zero_mem' := ⟨0, N.zero_mem, (fullRankSB k a (a + b)).zero_mem, hzero⟩
      add_mem' := by
        rintro _ _ ⟨Φ, h1, h2, rfl⟩ ⟨Ψ, h3, h4, rfl⟩
        exact ⟨Φ + Ψ, N.add_mem h1 h3, (fullRankSB k a (a + b)).add_mem h2 h4, hadd Φ h2 Ψ h4⟩
      smul_mem' := by
        rintro c _ ⟨Φ, h1, h2, rfl⟩
        exact ⟨c • Φ, N.smul_mem c h1, (fullRankSB k a (a + b)).smul_mem c h2, hsmul c Φ⟩ }
  have hind : ∀ Ψ ∈ fullRankSB k a (a + b), fibre ν β a b Ψ ∈ indScal ν β a b := by
    intro Ψ hΨ
    refine ⟨?_, Llaw k a b ν β Ψ⟩
    have hle : stabSub ((repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + b)) k))) Ψ ≤
        stabSub (rightReg ℂ (GL (Fin (a + b)) k) ℂ) (fibre ν β a b Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + b)) k) ℂ h (fibre ν β a b Ψ) = fibre ν β a b Ψ
      funext x
      show fibre ν β a b Ψ (x * h) = fibre ν β a b Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (Lsmooth k a (a + b) ν β hβs Ψ hΨ.1)
  have hMle : M ≤ indScal ν β a b := by
    rintro _ ⟨Ψ, -, hΨ, rfl⟩
    exact hind Ψ hΨ
  have hMst : ∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M := by
    rintro _ ⟨Ψ, h1, h2, rfl⟩ h
    exact ⟨omA ν β 1 h Ψ, hNst h Ψ h1, hS0 h Ψ h2, funext fun x => fibre_omA ν β a b h Ψ x⟩
  rcases Lirr HB k a b ν β hνs hνu hβs hβu M hMle hMst with h0 | hT
  · left
    intro Ψ hΨN hΨr
    have hΨ : Ψ ∈ fullRankSB k a (a + b) := ⟨hNSB hΨN, hΨr⟩
    have hm : fibre ν β a b Ψ ∈ M := ⟨Ψ, hΨN, hΨ, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact Lker k a b ν β hνs hβs Ψ hΨ hm
  · right
    intro Φ hΦ hΦr
    have hΦS : Φ ∈ fullRankSB k a (a + b) := ⟨hΦ, hΦr⟩
    obtain ⟨Ψ, hΨN, hΨS, hZ⟩ := hT (hind Φ hΦS)
    have hd : Φ - Ψ ∈ coinv ν β a (a + b) := by
      refine Lker k a b ν β hνs hβs _ ((fullRankSB k a (a + b)).sub_mem hΦS hΨS) ?_
      rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, hadd Φ hΦS _ ((fullRankSB k a (a + b)).smul_mem _ hΨS),
        hsmul, hZ]
      simp
    have := N.add_mem (hCN hd) hΨN
    simpa using this

theorem coinv_or_fullRank_le : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) :=
  of_parts GlobalTheory.T.induced_scalar_irreducible GlobalTheory.T.fibre_mem_induced_space GlobalTheory.T.isOpen_stabilizer_schwartzBruhat GlobalTheory.T.integrable_full_rank_fibre GlobalTheory.T.fibre_zero_mem_coinvariants

end GlobalTheory.RankFibre
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff




theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro F E _ _ _ _ _ nS nT N e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Formalism.IndefR.DatumF.WOF F E nS nT :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = Formalism.IndefR.DatumF.ratWF x := fun x => rfl
  let L : Matrix (Fin nT) (Fin nS) E →ₗ[F] GlobalTheory.ThetaTransform.VA F N := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (Formalism.IndefR.DatumF.ratWF x) := fun x => by rw [← hI]; rfl
  let r : (Fin N → F) →ₗ[F] (Fin N → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((Fin N → F) × (Fin N → F)) →ₗ[F] GlobalTheory.ThetaTransform.VA F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin nT) * Fintype.card (Fin nS) * Module.finrank F E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem addHom_eq_of_basis {R S M ι : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (ρ : R →+* S) (F₁ F₂ : M →+ S)
    (h₁ : ∀ (c : R) x, F₁ (c • x) = ρ c * F₁ x) (h₂ : ∀ (c : R) x, F₂ (c • x) = ρ c * F₂ x)
    (h : ∀ i, F₁ (b i) = F₂ (b i)) (x : M) : F₁ x = F₂ x := by
  have hx : x ∈ Submodule.span R (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | smul c y _ hy => rw [h₁, h₂, hy]

theorem wittMap_comp (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k'']
    (σ : k →+* k') (τ : k' →+* k'') (x : WittVector p k) :
    WittVector.map (τ.comp σ) x = WittVector.map τ (WittVector.map σ x) := by
  ext n
  simp [WittVector.map_coeff]

end GlobalTheory.Dieu.EtFromConn

theorem GlobalTheory.Dieu.EtFromConn.isTr_comp : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' k'' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] (σ : k →+* k') (τ : k' →+* k'') (υ : k →+* k'') (G'' : PDivGroup p k'') (G' : PDivGroup p k') (G : PDivGroup p k) (h'' : G''.IsEt) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G), (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ (l : Mod B G h) (l' : Mod B G' h') (l'' : Mod B G'' h''), IsTr B σ h' h s l l' → IsTr B τ h'' h' t l' l'' → IsTr B υ h'' h u l l'' := by
  intro p _ B k k' k'' _ _ _ _ _ _ _ _ _ σ τ υ G'' G' G h'' h' h s t u hu l l' l'' hs ht
  have hυ : υ = τ.comp σ := by
    ext r
    have e := congrArg (Coalgebra.counit (R := k'')) (hu 0 (algebraMap k (G.A 0) r))
    rw [(u.app 0).counit_map, (t.app 0).counit_map, (s.app 0).counit_map,
      Bialgebra.counit_algebraMap] at e
    simpa using e
  subst hυ
  obtain rfl : u = t.comp s := SemiHom.ext_apply hu
  letI iσ : Algebra k k' := σ.toAlgebra
  letI iτ : Algebra k' k'' := τ.toAlgebra
  letI iυ : Algebra k k'' := (τ.comp σ).toAlgebra
  dsimp only [IsTr] at hs ht ⊢
  obtain ⟨hb, lb, hlb, hl'⟩ := hs
  obtain ⟨hb', lb', hlb', hl''⟩ := ht
  have hD := dual_conn h
  have hbu : (G.dual.baseChange k'').IsConn := (baseChange_isConn_isEt p k k'' G.dual).1 hD
  haveI := B.free G.dual hD
  haveI := B.finite G.dual hD
  let b := Module.Free.chooseBasis (WittVector p k) (B.M G.dual hD)
  obtain ⟨bu, hbu_eq⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k k'' G.dual hD hbu _ b
  obtain ⟨bk, hbk_eq⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k k' G.dual hD hb _ b
  let lbu : Module.Dual (WittVector p k'') (B.M (G.dual.baseChange k'') hbu) :=
    bu.constr (WittVector p k'') fun i => WittVector.map (τ.comp σ) (l (b i))
  have hlbu : ∀ x, lbu (B.smap hbu hD (G.dual.toBase k'') x) = WittVector.map (τ.comp σ) (l x) := by
    intro x
    refine addHom_eq_of_basis b (WittVector.map (τ.comp σ))
      ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hD (G.dual.toBase k'')))
      ((WittVector.map (τ.comp σ)).toAddMonoidHom.comp (l : _ →+ WittVector p k)) ?_ ?_ ?_ x
    · intro c x
      show lbu (B.smap hbu hD (G.dual.toBase k'') (c • x)) = _ * lbu (B.smap hbu hD (G.dual.toBase k'') x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
      rfl
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe]
      rw [← hbu_eq, Module.Basis.constr_basis]
  refine ⟨hbu, lbu, hlbu, fun y => ?_⟩

  let β : G'.baseChange k'' ⟶ G.baseChange k'' :=
    SemiHom.lift (((G'.toBase k'').comp s : SemiHom ((algebraMap k' k'').comp σ) _ G) :
      SemiHom (algebraMap k k'') _ G)
  have hβ : ∀ n (b : G.A n), β.app n ((G.toBase k'').app n b) = (G'.toBase k'').app n (s.app n b) := by
    intro n b
    rw [toBase_app, SemiHom.lift_app, one_smul]
    rfl
  have hlift : (t.comp s).lift = t.lift ≫ β := baseChange_hom_ext fun n a => by
    rw [SemiHom.lift_app, one_smul, comp_app, BialgHom.comp_apply, ← toBase_app, hβ, toBase_app,
      SemiHom.lift_app, one_smul]
    rfl
  let φs := (PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift
  let φt := (PerfdLat.dualBaseChange k'' G').inv ≫ dualHom G'' (G'.baseChange k'') t.lift
  let ψ : G.dual.baseChange k'' ⟶ G'.dual.baseChange k'' :=
    (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom _ _ β ≫ (PerfdLat.dualBaseChange k'' G').hom
  have hψ : (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom G'' (G.baseChange k'') (t.comp s).lift =
      ψ ≫ φt := by
    simp only [hlift, dualHom_comp, ψ, φt, Category.assoc, Iso.hom_inv_id_assoc]
  let ρ : SemiHom τ (G.dual.baseChange k'') (G.dual.baseChange k') :=
    (G.dual.toBase k'').liftOver τ (fun _ => rfl)
  have hρ : ∀ n (χ : G.dual.A n), ρ.app n ((G.dual.toBase k').app n χ) = (G.dual.toBase k'').app n χ := by
    intro n χ
    rw [toBase_app, SemiHom.liftOver_app, map_one, one_smul]
  have hinv : ∀ {O' : Type} [Field O'] [Algebra k O'] (n : ℕ) (Z : (G.baseChange O').dual.A n),
      (PerfdLat.dualBaseChange O' G).hom.app n ((PerfdLat.dualBaseChange O' G).inv.app n Z) = Z :=
    fun {O'} _ _ n Z => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange O' G).hom_inv_id) Z
  have hinj : ∀ n, Function.Injective ((PerfdLat.dualBaseChange k'' G).hom.app n) := fun n x y hxy => by
    have e : ∀ x, (PerfdLat.dualBaseChange k'' G).inv.app n ((PerfdLat.dualBaseChange k'' G).hom.app n x) = x :=
      fun x => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange k'' G).inv_hom_id) x
    rw [← e x, ← e y, hxy]
  have hE : ∀ n (y : (G.dual.baseChange k').A n) (b : G.A n),
      ((PerfdLat.dualBaseChange k'' G).hom.app n (ρ.app n y)).ofConv ((G.toBase k'').app n b) =
        τ (((PerfdLat.dualBaseChange k' G).hom.app n y).ofConv ((G.toBase k').app n b)) := by
    intro n y b
    induction y using baseChange_induction k' (G := G.dual) n with
    | h0 => simp
    | h1 r χ =>
      rw [(ρ.app n).smul_map, map_smul, WithConv.ofConv_smul, LinearMap.smul_apply, map_smul, WithConv.ofConv_smul,
        LinearMap.smul_apply, hρ, dualBaseChange_toBase, dualBaseChange_toBase, smul_eq_mul, smul_eq_mul,
        map_mul]
      rfl
    | h2 z w hz hw =>
      rw [map_add (f := _), map_add (f := _), WithConv.ofConv_add, LinearMap.add_apply, map_add (f := _), WithConv.ofConv_add, LinearMap.add_apply,
        map_add, hz, hw]
  have hC : ∀ n a, ψ.app n ((G'.dual.toBase k'').app n a) = ρ.app n (φs.app n a) := by
    intro n a
    apply hinj n
    apply WithConv.ofConv_injective
    refine LinearMap.ext fun x => ?_
    induction x using baseChange_induction k'' (G := G) n with
    | h0 => simp
    | h1 r b =>
      rw [map_smul, map_smul, hE]
      congr 1
      change ((PerfdLat.dualBaseChange k'' G).hom.app n ((PerfdLat.dualBaseChange k'' G).inv.app n
        (CartierDual.map (β.app n) ((PerfdLat.dualBaseChange k'' G').hom.app n ((G'.dual.toBase k'').app n a))))).ofConv
          ((G.toBase k'').app n b) = τ (((PerfdLat.dualBaseChange k' G).hom.app n ((PerfdLat.dualBaseChange k' G).inv.app n
            (CartierDual.map (s.lift.app n) a))).ofConv ((G.toBase k').app n b))
      rw [hinv, hinv, CartierDual.map_apply, CartierDual.map_apply, hβ, dualBaseChange_toBase, toBase_app,
        SemiHom.lift_app, one_smul]
      rfl
    | h2 z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw]
  have hD' : ∀ v, lbu (B.smap hbu hb ρ v) = WittVector.map τ (lb v) := by
    intro v
    refine addHom_eq_of_basis bk (WittVector.map τ) ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hb ρ))
      ((WittVector.map τ).toAddMonoidHom.comp (lb : _ →+ WittVector p k')) ?_ ?_ ?_ v
    · intro c x
      show lbu (B.smap hbu hb ρ (c • x)) = _ * lbu (B.smap hbu hb ρ x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      show lbu (B.smap hbu hb ρ (bk i)) = WittVector.map τ (lb (bk i))
      rw [hbk_eq, hlb, ← B.smap_comp hbu hb hD (G.dual.toBase k') ρ (G.dual.toBase k'')
        (fun n a => (hρ n a).symm), hlbu, wittMap_comp]
  have hA : ∀ z, lb' z = lbu (B.map hbu hb' ψ z) := by
    haveI := B.free G'.dual (dual_conn h')
    haveI := B.finite G'.dual (dual_conn h')
    let b' := Module.Free.chooseBasis (WittVector p k') (B.M G'.dual (dual_conn h'))
    obtain ⟨b'', hb''⟩ := GlobalTheory.T.dieudonne_baseChange_basis p _ B k' k'' G'.dual (dual_conn h') hb' _ b'
    have key := b''.ext (f₁ := lb') (f₂ := lbu.comp (B.map hbu hb' ψ)) fun i => by
      rw [hb'', hlb', hl', LinearMap.comp_apply]
      change _ = lbu (B.smap hbu hb' (SemiHom.ofHom ψ)
        (B.smap hb' (dual_conn h') (G'.dual.toBase k'') (b' i)))
      rw [← B.smap_comp hbu hb' (dual_conn h') (G'.dual.toBase k'') (SemiHom.ofHom ψ)
        (ρ.comp (SemiHom.ofHom φs)) (fun n a => (hC n a).symm),
        B.smap_comp hbu hb (dual_conn h') (SemiHom.ofHom φs) ρ (ρ.comp (SemiHom.ofHom φs)) (fun _ _ => rfl),
        hD']
      rfl
    exact fun z => LinearMap.congr_fun key z
  rw [hl'', hA, hψ]
  exact congrArg lbu (B.smap_comp hbu hb' (dual_conn h'') (SemiHom.ofHom φt) (SemiHom.ofHom ψ)
    (SemiHom.ofHom (ψ ≫ φt)) (fun _ _ => rfl) y).symm
end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW
open scoped FourierTransform

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IsRapidFamInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ) :
    Prop :=
  (∀ i j, Measurable fun x =>(γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E)),
    (∀ i j, Measurable fun x =>(γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) →
      Measurable (fun p : X₀ × X =>k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X =>η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x =>‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htInf q ^ M

def sandCLMInf (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    (Fin n → Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>(A * Matrix.of x * B) i j
      map_add' := fun x y =>by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x =>by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

theorem sandCLMInf_apply (A B : Matrix (Fin n) (Fin n) (Cinf E)) (x : Fin n → Fin n → Cinf E) (i j : Fin n) :
    sandCLMInf A B x i j = (A * Matrix.of x * B) i j := rfl

def jacInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ := ∏ w : InfinitePlace E, Complex.normSq (x.det w) ^ n


open Classical in
def secKInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q then
    ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEtaInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → Cinf E))
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)).comp L))

theorem jacInf_mul (x y : Matrix (Fin n) (Fin n) (Cinf E)) : jacInf (x * y) = jacInf x * jacInf y := by
  simp only [jacInf, Matrix.det_mul, Pi.mul_apply, map_mul, mul_pow, Finset.prod_mul_distrib]

end GlobalTheory.JSW.MirCinf
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_rightInv | exact GlobalTheory.JSW.MirSemi.locSpan_rightInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_rightInv <;> assumption)
end
