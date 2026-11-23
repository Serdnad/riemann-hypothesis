module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.StabFin

section General

variable {A R n : Type} [CommRing A] [CommRing R] [Algebra R A] [Fintype n] [DecidableEq n]

theorem mem_stab_conj {L S : Submodule R (n → A)} {b : GL n A} (h : ∀ y, y ∈ S ↔ b.1 *ᵥ y ∈ L) (x : GL n A) :
    x ∈ Formalism.UG.stabGL L ↔ b⁻¹ * x * b ∈ Formalism.UG.stabGL S := by
  have key : ∀ y, (b⁻¹ * x * b).1 *ᵥ y ∈ S ↔ x.1 *ᵥ (b.1 *ᵥ y) ∈ L := fun y => by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  constructor
  · intro hx y
    rw [key, h]
    exact hx _
  · intro hx y
    have h1 := hx ((b⁻¹).1 *ᵥ y)
    rw [key, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1


omit [CommRing R] [Algebra R A] in
theorem conj_eq_of_smul {m m' : GL n A} {w : A} (h : m.1 = w • m'.1) (z : GL n A) :
    m⁻¹ * z * m = m'⁻¹ * z * m' := by
  have hc : m * m'⁻¹ * z = z * (m * m'⁻¹) := by
    apply Units.ext
    have e : (m * m'⁻¹).1 = w • (1 : Matrix n n A) := by
      rw [Units.val_mul, h, Matrix.smul_mul, Units.mul_inv]
    rw [Units.val_mul _ z, Units.val_mul z, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc m⁻¹ * z * m = m⁻¹ * (z * (m * m'⁻¹)) * m' := by group
    _ = m⁻¹ * (m * m'⁻¹ * z) * m' := by rw [hc]
    _ = m'⁻¹ * z * m' := by group

end General

theorem mem_stab_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)} (h : ∀ i j, m.1 i j ∈ intLoc F E v)
    (h' : ∀ i j, (m⁻¹).1 i j ∈ intLoc F E v) : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  have key : ∀ (M : Matrix (Fin N) (Fin N) (Fv F v ⊗[F] E)), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y, y ∈ latLoc F (stdLattice E N) v → M *ᵥ y ∈ latLoc F (stdLattice E N) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  intro y
  refine ⟨key _ h y, fun hy => ?_⟩
  have h1 := key _ h' _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1

theorem mem_stab_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), _root_.GlobalTheory.AdelicU.IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  intro F E _ _ _ _ _ N Λ b M M' u hb hM' hM v x
  have hs : Formalism.UG.bc (compFin F E v) M' ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
    refine mem_stab_std (fun i j => (hM' v i j).1) (fun i j => ?_)
    rw [← map_inv]
    exact (hM' v i j).2
  have he : (Formalism.UG.bc (compFin F E v) M).1 =
      compFin F E v (u : AF F ⊗[F] E) • (Formalism.UG.bc (compFin F E v) M').1 := by
    ext i j
    change compFin F E v (M.1 i j) = compFin F E v (u : AF F ⊗[F] E) * compFin F E v (M'.1 i j)
    rw [hM, ← map_mul]
    rfl
  rw [mem_stab_conj (S := latLoc F (stdLattice E N) v) (b := Formalism.UG.bc (compFin F E v) b)
    (fun y => mem_latLoc_stdLattice.trans (hb v y)) x, map_mul, mul_inv_rev]
  set β := Formalism.UG.bc (compFin F E v) b
  have e : (Formalism.UG.bc (compFin F E v) M)⁻¹ * β⁻¹ * x * (β * Formalism.UG.bc (compFin F E v) M) =
      (Formalism.UG.bc (compFin F E v) M)⁻¹ * (β⁻¹ * x * β) * Formalism.UG.bc (compFin F E v) M := by group
  rw [e, conj_eq_of_smul he, Subgroup.mul_mem_cancel_right _ hs, Subgroup.mul_mem_cancel_left _ (inv_mem hs)]

end GlobalTheory.StdUnn.StabFin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.FinRank

theorem span_eval_eq_top {α : Type*} (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E] :
    Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) = ⊤ := by
  set Sp := Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype)
  have hb : Sp.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext u
    have := hx _ (Submodule.subset_span ⟨u, rfl⟩)
    simpa using this
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sp)
  rw [← this, hb, Submodule.dualAnnihilator_bot]

theorem sum_prod_of_slices {α β : Type*} (C : α → β → ℂ) (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E]
    (E' : Submodule ℂ (β → ℂ)) (hl : ∀ v, (fun u => C u v) ∈ E) (hr : ∀ u, C u ∈ E') :
    ∃ (n : ℕ) (e : Fin n → α → ℂ) (g : Fin n → β → ℂ), (∀ i, e i ∈ E) ∧ (∀ i, g i ∈ E') ∧
      ∀ u v, C u v = ∑ i, e i u * g i v := by
  let b := Module.finBasis ℂ E
  let ev : α → Module.Dual ℂ E := fun u => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype
  have hsurj : ∀ φ : Module.Dual ℂ E, ∃ a : α →₀ ℂ, Finsupp.linearCombination ℂ ev a = φ := by
    intro φ
    have h1 : φ ∈ LinearMap.range (Finsupp.linearCombination ℂ ev) := by
      rw [Finsupp.range_linearCombination]
      rw [span_eval_eq_top E]
      trivial
    exact h1
  choose a ha using fun i => hsurj (b.coord i)
  refine ⟨Module.finrank ℂ E, fun i => (b i : α → ℂ), fun i => ∑ u ∈ (a i).support, a i u • C u,
    fun i => (b i).2, fun i => Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (hr u), ?_⟩
  intro u v
  have hs := b.sum_repr ⟨fun u => C u v, hl v⟩
  have h2 := congrArg (fun w : E => (w : α → ℂ) u) hs
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have h3 := congrArg (fun φ : Module.Dual ℂ E => φ ⟨fun u => C u v, hl v⟩) (ha i)
  simp only [Module.Basis.coord_apply] at h3
  rw [← h3, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  simp [ev, Finset.sum_apply]

end GlobalTheory.SeeSaw.FinRank

namespace GlobalTheory.SeeSaw.FinRank

theorem biVac_sum_fock : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  intro D hF ψ θ hθ A S A' x y z hx hy hz k k' hk hk' χ χ' C hC hχ hχ'
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k hk χ
  obtain ⟨W', _, hWf'⟩ := hF ψ θ hθ S A' y z hy hz k' hk' χ'
  haveI := hW
  let T := pureTensorO ψ θ A S x.s y.s x.B y.B k.vac
  let T' := pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac
  have hl : ∀ v, (fun u => C u v) ∈ W.map T := by
    intro v
    obtain ⟨P, hP, e⟩ := hWf _ (hC.left v).1 (hC.left v).2 (fun a ha hc => hχ a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hr : ∀ u, C u ∈ W'.map T' := by
    intro u
    obtain ⟨P, hP, e⟩ := hWf' _ (hC.right u).1 (hC.right u).2 (fun b hb hc => hχ' b hb hc u)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  obtain ⟨n, e, g, he, hg, hs⟩ := sum_prod_of_slices C (W.map T) (W'.map T') hl hr
  choose P _ hP using fun i => Submodule.mem_map.1 (he i)
  choose P' _ hP' using fun i => Submodule.mem_map.1 (hg i)
  refine ⟨n, P, P', fun u v => ?_⟩
  rw [hs u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  show e i u * g i v = T (P i) u * T' (P' i) v
  rw [hP i, hP' i]

end GlobalTheory.SeeSaw.FinRank

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf



namespace GlobalTheory.AdForm.KerVal

theorem eval_jetLin_jetC {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℂ) (Θ : VCx ι a b → ℂ) (y : ι → Matrix (Fin b) (Fin b) ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin b × Fin b => y x.1 x.2.1 x.2.2) (jetLin (jetC c Θ) Q) =
      jetL c Θ (MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m r =>
    have h1 : jetLin (jetC c Θ) (MvPolynomial.monomial m r) = r • MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
        (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) := by
      have := (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ).constr_basis ℂ (fun m =>
        (MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
          (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      rw [show (MvPolynomial.monomial m r : MvPolynomial _ ℂ) = r • MvPolynomial.monomial m 1 by simp [MvPolynomial.smul_monomial], map_smul]
      congr 1
    have h2 : MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) (MvPolynomial.monomial m r) = (r * ∏ x : ι × Fin b × Fin b, y x.1 x.2.1 x.2.2 ^ m (Sum.inl x)) •
          MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) 1 := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc]
    rw [h1, h2, MvPolynomial.smul_eval, LinearMap.map_smul, jetL_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp
    ring

theorem kmap_val {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ) (hab : B.R.N i ≤ B.R.N (i + 1)) (c : (I.chain l u a).cls i)
    (c' : (I.chain l u a).cls (i + 1)) (ψ : (I.chain l u a).Y i → ℂ) (Q : PY (I.rec7 l Z).what₂.Tau (B.R.N i))
    (hψ : ∀ y : (I.chain l u a).Y i, ψ y = evalAt y.1 Q * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ))
    (y' : (I.chain l u a).Y (i + 1)) :
    (I.chain l u a).Kmap i c c' ψ y' =
      A.abelian₂ i c c' (subY hab y'.1 Q) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  have h1 : (I.chain l u a).sharp i ψ = fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0
      (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N i)).1 τ)⁻¹) Q := by
    funext y
    have e := hψ y
    show (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ψ y =
      (∏ τ, ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 τ).det ^ (0 : ℤ)) *
        MvPolynomial.eval (fun x => ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 x.1) x.2.1 x.2.2) Q
    rw [e]
    simp only [inv_one, Matrix.one_mul, zpow_zero, Finset.prod_const_one, one_mul]
    have : (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (y.2 τ).ne_zero)]
    exact (mul_left_comm _ _ _).trans ((congrArg _ this).trans (mul_one _))
  have h2 : (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y' =
      jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) := by
    rw [h1]
    refine Eq.trans ?_ ((eval_jetLin_jetC (ι := B.fields.Tau) I.J.cD _ y'.1 (subD ℂ _ _ _ Q)).trans
      (congrArg _ (subY_eq_subD hab y'.1 Q).symm))
    have h3 := Formalism.L2.Col.polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i)) Q
    refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ((I.chIn u a).jet i c c' P) y') h3).trans ?_
    simp [fnOf, jetMap]
    rfl
  show ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * ((∏ τ, (y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ *
    (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y') =
    ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) *
      ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ)
  rw [h2]
  simp only [_root_.zpow_neg, Finset.prod_inv_distrib]
  ring

theorem kernel_classSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  intro B X I _ _ l Z u a Ch A _ i _ hab φ Fc hφ c' y'
  haveI : Fintype ((I.chain l u a).cls i) := (I.chain l u a).clsFin i
  unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, kmap_val A i hab c c' (φ c) (Fc c) (hφ c) y', ColumnChain.wt]
  ring

end GlobalTheory.AdForm.KerVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Scale

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T a (c • f) = c • comb ψ S T a f := by
  simp only [comb, heisO_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S →₀ ℂ) (a' : WO S A' →₀ ℂ) (c : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' a a' (c • C) = c • biComb ψ A S A' a a' C := by
  funext u v
  simp only [biComb]
  have h1 : (fun u' => comb ψ S A' a' ((c • C) u') v) = c • fun u' => comb ψ S A' a' (C u') v := by
    funext u'
    show comb ψ S A' a' (c • C u') v = c * comb ψ S A' a' (C u') v
    rw [comb_smul]; rfl
  rw [h1, comb_smul]; rfl

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul, hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) :=
  ⟨fun u hu => by rw [heisO_smul, hf.1 u hu], fun e' he u hu hh => by rw [heisO_smul, hf.2 e' he u hu hh]⟩

theorem isBiVac_smul {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Set (Fin A.rank → D.host.E)}
    {LS : Set (Fin S.rank → D.host.E)} {LA' : Set (Fin A'.rank → D.host.E)} (c : ℂ) {C : WO A S → WO S A' → ℂ}
    (h : IsBiVac ψ A S A' LA LS LA' C) : IsBiVac ψ A S A' LA LS LA' (c • C) := by
  refine ⟨continuous_const.mul h.cont, ?_, ?_⟩
  · intro v
    have e : (fun u => (c • C) u v) = c • fun u => C u v := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.left v).1, isLatVac_smul c (h.left v).2⟩
  · intro u
    have e : (c • C) u = c • C u := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.right u).1, isLatVac_smul c (h.right u).2⟩

theorem isBiSmooth_smul {A S A' : HSp D} (c : ℂ) {C : WO A S → WO S A' → ℂ} (h : IsBiSmooth C) :
    IsBiSmooth (c • C) :=
  fun n L L' hL hL' h0 h0' u v => by
    show ContDiff ℝ _ fun t => c * C (u + L t) (v + L' t)
    exact ContDiff.mul contDiff_const (h n L L' hL hL' h0 h0' u v)

end GlobalTheory.SeeSaw.Scale

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSumProof

variable {D : D7}

theorem om_zero_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ hf)

theorem liftSum : ∀ D : D7, LiftSum D := by
  intro D ψ θ hθ S T x y hx hy k hk P
  obtain ⟨χS, χT, hω⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hk.vac.1
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hcomb : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 k.vac hvac (WO S T) k.c.support id k.c (fun u hu => hk.fin u hu)
  have hpt : IsThetaFunO ψ S T (k.pt ψ θ x y P) :=
    GlobalTheory.FockTheta.ptStable D ψ θ hψ hθ S T x.s y.s x.B y.B _ P hcomb

  have key : ∀ φ : GA D S → ℂ, IsContAut S φ →
      (∀ h, IntegrableOn (fun g => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) x.vol.𝓕 x.vol.μ) ∧
      Continuous fun h => ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ := by
    intro φ hφ
    have hc : Continuous (Function.uncurry fun (g : GA D S) (h : GA D T) => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) :=
      (hω.om_cont _ hpt 0).mul (hφ.2.comp continuous_fst)
    have hinv : ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T),
        k.om (γ * g, h) (k.pt ψ θ x y P) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y P) 0 * φ g := by
      intro γ hγ g h
      have e := om_zero_rat hω hpt hγ (one_mem (GQ T)) g h
      rw [one_mul] at e
      rw [e, hφ.1 γ hγ g]
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hx.cpt x.vol (GA D T) _ hc hinv
    exact ⟨h1, h2⟩
  refine ⟨hpt, fun φ hφ => ⟨fun γ' hγ' h => ?_, ?_⟩, fun I s a φ hφ => ?_⟩
  · show ∫ g in x.vol.𝓕, k.om (g, γ' * h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ =
      ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ
    congr 1
    funext g
    have e := om_zero_rat hω hpt (one_mem (GQ S)) hγ' g h
    rw [one_mul] at e
    rw [e]
  · exact (key φ hφ).2
  · funext h
    show ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * (∑ i ∈ s, a i • φ i) g ∂x.vol.μ =
      (∑ i ∈ s, a i • fun h' => ∫ g in x.vol.𝓕, k.om (g, h') (k.pt ψ θ x y P) 0 * φ i g ∂x.vol.μ) h
    rw [Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : (fun g => ∑ i ∈ s, k.om (g, h) (k.pt ψ θ x y P) 0 * (a i * φ i g)) =
        fun g => ∑ i ∈ s, a i * (k.om (g, h) (k.pt ψ θ x y P) 0 * φ i g) := by
      funext g
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum s (fun i hi => ((key (φ i) (hφ i hi)).1 h).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul (a i) _

end GlobalTheory.SeeSaw.LiftSumProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end
