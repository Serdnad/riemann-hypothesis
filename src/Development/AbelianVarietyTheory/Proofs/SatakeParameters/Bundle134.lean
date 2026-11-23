module

public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle125
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.LogExist

variable {l : ℕ} [Fact l.Prime]

def logSum (w : Per.AinfP l) (n : ℕ) : Per.AinfP l :=
  ∑ k ∈ Finset.range n, (-1) ^ k * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) * w ^ (k + 1)

theorem logSum_succ (w : Per.AinfP l) (n : ℕ) :
    logSum w (n + 1) = logSum w n + (-1) ^ n * Ring.inverse (((n + 1 : ℕ) : Per.AinfP l)) * w ^ (n + 1) := by
  simp only [logSum, Finset.sum_range_succ]

theorem logSum_cauchy {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    logSum w n ≡ logSum w (n + 1) [SMOD (Per.kerP l ^ n • ⊤ : Submodule (Per.AinfP l) (Per.AinfP l))] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, logSum_succ, sub_add_cancel_left]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hw _)

def logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : Per.BdRp l :=
  (GlobalTheory.RingIface.exists_bdRp_equiv l).choose.symm (AdicCompletion.mk (Per.kerP l) (Per.AinfP l)
    (AdicCompletion.AdicCauchySequence.mk (Per.kerP l) (Per.AinfP l) (logSum w) (logSum_cauchy hw)))

theorem ev_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    Per.ev l n (logP hw) = Ideal.Quotient.mk _ (logSum w n) := by
  rw [← (GlobalTheory.RingIface.exists_bdRp_equiv l).choose_spec.2, logP, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk]
  rfl

theorem factorial_mul_logSum (w : Per.AinfP l) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l) * logSum w n =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) := by
  rw [logSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : n.factorial / (k + 1) * (k + 1) = n.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (Nat.succ_pos k) hkn)
  have hu : ((k + 1 : ℕ) : Per.AinfP l) * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) = 1 :=
    Ring.mul_inverse_cancel _ (GlobalTheory.RingBasics.isUnit_nat l _ (Nat.succ_ne_zero k))
  have hc : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * ((k + 1 : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, hd]
  rw [hc]
  linear_combination (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) * hu

theorem isLogP_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : IsLogP w (logP hw) := by
  intro n
  rw [ev_logP, ← factorial_mul_logSum, map_mul, map_natCast]

theorem exists_isLogP : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u :=
  fun _ _ _ hw => ⟨logP hw, isLogP_logP hw⟩

end GlobalTheory.Pst.LogExist
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.eq_top_of_forall_complexPoints_mem_opens : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  first | (exact @GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (exact GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (intros; apply GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.finite_complexPoints_transversal_zeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ (k : ℕ) (φ : Fin k → Γ(X, U)), {z : CxPts p (RingHom.id ℂ) | ∃ hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U,
      (∀ j, CxPts.evHom hz (φ j) = 0) ∧
        RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range φ) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2}.Finite := by
  first | (exact @GlobalTheory.TransvZeros.finite_transv_zeros) | (exact GlobalTheory.TransvZeros.finite_transv_zeros) | (intros; apply GlobalTheory.TransvZeros.finite_transv_zeros  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  first | (exact @GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (exact GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (intros; apply GlobalTheory.ChartSard.null_negEv_of_det_eq_zero  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JacSpan

theorem ker_le_span_sup {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) {d : ℕ} (δ : Fin d → A →+ ℂ)
    (hmul : ∀ b f g, δ b (f * g) = e f * δ b g + e g * δ b f)
    (hc : ∀ b (c : ℂ), δ b (algebraMap ℂ A c) = 0) (g : Fin d → A)
    (hgs : ∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2)
    (φ : Fin d → A) (hdet : (Matrix.of fun a b => δ b (φ a)).det ≠ 0) :
    RingHom.ker e ≤ Ideal.span (Set.range fun j => φ j - algebraMap ℂ A (e (φ j))) ⊔
      RingHom.ker e ^ 2 := by
  classical
  have hsq : ∀ b, ∀ x ∈ RingHom.ker e ^ 2, δ b x = 0 := by
    intro b x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [hmul, RingHom.mem_ker.1 hx, RingHom.mem_ker.1 hy, zero_mul, zero_mul, add_zero]
    · rw [map_add (f := _), hx, hy, add_zero]
  have hsmul : ∀ b (c : ℂ) (x : A), δ b (c • x) = c * δ b x := by
    intro b c x
    rw [Algebra.smul_def, hmul, hc, he, mul_zero, add_zero]
  set φ' : Fin d → A := fun j => φ j - algebraMap ℂ A (e (φ j)) with hφ'
  have hφ'e : ∀ j, e (φ' j) = 0 := fun j => by simp only [hφ', map_sub, he, sub_self]
  choose C hC using fun j => hgs (φ' j) (hφ'e j)
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun k b => δ b (g k)
  have hJ : (Matrix.of fun a b => δ b (φ a)) = Matrix.of C * M := by
    ext a b
    have h1 := hsq b _ (hC a)

    rw [map_sub, map_sum] at h1
    simp only [hsmul] at h1
    have h2 : δ b (φ' a) = δ b (φ a) := by simp only [hφ', map_sub, hc, sub_zero]
    rw [Matrix.of_apply, Matrix.mul_apply, ← h2]
    simp only [M, Matrix.of_apply]
    linear_combination h1
  have hdetC : (Matrix.of C).det ≠ 0 := by
    rw [hJ, Matrix.det_mul] at hdet
    exact left_ne_zero_of_mul hdet
  have hu : IsUnit (Matrix.of C).det := isUnit_iff_ne_zero.2 hdetC
  intro a ha
  obtain ⟨β, hβ⟩ := hgs a (RingHom.mem_ker.1 ha)
  set γ := Matrix.vecMul β (Matrix.of C)⁻¹ with hγdef
  have hγ : Matrix.vecMul γ (Matrix.of C) = β := by
    rw [hγdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hsum : ∑ j, γ j • ∑ k, C j k • g k = ∑ k, β k • g k := by
    rw [← hγ]
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
      Matrix.of_apply]
    exact Finset.sum_comm
  have hspan : ∑ j, γ j • φ' j ∈ Ideal.span (Set.range φ') :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hrest : a - ∑ j, γ j • φ' j ∈ RingHom.ker e ^ 2 := by
    have h3 : a - ∑ j, γ j • φ' j =
        (a - ∑ k, β k • g k) - ∑ j, γ j • (φ' j - ∑ k, C j k • g k) := by
      rw [← hsum]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h3]
    exact sub_mem hβ (Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hC j))
  have h4 : a = (a - ∑ j, γ j • φ' j) + ∑ j, γ j • φ' j := by abel
  rw [h4]
  exact add_mem (Ideal.mem_sup_right hrest) (Ideal.mem_sup_left hspan)

end GlobalTheory.JacSpan


open GlobalTheory.ChartGlue in
theorem GlobalTheory.JacSpan.ker_le_span_jac : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU ch φ z hzc hz hdet
  obtain ⟨g, _, hgs, _⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d U hU z hz
  have hd : ∀ f : Γ(X, U), DifferentiableAt ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) :=
    fun f => ch.differentiableAt_ev f hzc hz
  have hn : ∀ᶠ v in nhds (ch.e z), ch.e.symm v ∈ CxPts.ptsIn p (RingHom.id ℂ) U :=
    Filter.eventually_of_mem ((isOpen_over ch.e (CxPts.isOpen_ptsIn U)).mem_nhds
      (mem_over ch.e hzc hz)) fun _ h => h.2
  let δ : Fin d → Γ(X, U) →+ ℂ := fun b => AddMonoidHom.mk' (fun f =>
      fderiv ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) (EuclideanSpace.single b 1))
    (fun f g => by
      have e : CxPts.ev p (RingHom.id ℂ) U (f + g) ∘ ch.e.symm =
          (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) + (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
        funext fun v => CxPts.ev_add _ _ _
      simp only [e, fderiv_add (hd f) (hd g), ContinuousLinearMap.add_apply])
  have hmul : ∀ b (f g : Γ(X, U)), δ b (f * g) =
      CxPts.evHom hz f * δ b g + CxPts.evHom hz g * δ b f := by
    intro b f g
    have e : CxPts.ev p (RingHom.id ℂ) U (f * g) ∘ ch.e.symm =
        (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) * (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
      funext fun v => CxPts.ev_mul _ _ _
    simp only [δ, AddMonoidHom.mk'_apply, e, fderiv_mul (hd f) (hd g), Function.comp_apply,
      ch.e.left_inv hzc, CxPts.ev_eq hz, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : ∀ b (c : ℂ), δ b (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) = 0 := by
    intro b c
    have e : CxPts.ev p (RingHom.id ℂ) U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) ∘ ch.e.symm
        =ᶠ[nhds (ch.e z)] fun _ => c := hn.mono fun v hv => CxPts.ev_algX hv c
    simp only [δ, AddMonoidHom.mk'_apply]
    rw [e.fderiv_eq]
    simp
  exact GlobalTheory.JacSpan.ker_le_span_sup (A := GlobalTheory.CechDR.Sec p U) (CxPts.evHom hz)
    (fun c => (CxPts.ev_eq hz _).symm.trans (CxPts.ev_algX hz c)) δ hmul hc g hgs φ hdet
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  first | (exact @GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (exact GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (intros; apply GlobalTheory.MaxPt.exists_cxPts_ker_eq  <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

theorem eqv_trans (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

theorem eqv_symm (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

theorem eqv_refl (ρ : Representation ℂ G V) : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_placing {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e e' : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π)) :=
  (Placing.parInd_jac_placing k α n m e e' _).1 _

theorem ind₂_congr {r t N : ℕ} (h : r + t = N) {V V' W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {σ₁ : Representation ℂ (GL (Fin r) k) V'}
    {π₂ : Representation ℂ (GL (Fin t) k) W} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : Nonempty (π₁.Equiv σ₁)) (φ₂ : Nonempty (π₂.Equiv σ₂)) :
    Nonempty ((ind₂ (stdSum h) (extTensor π₁ π₂)).Equiv (ind₂ (stdSum h) (extTensor σ₁ σ₂))) := by
  subst h
  exact φ₁.elim fun a => φ₂.elim fun b => ⟨LocGL.prod₂Equiv a b⟩

theorem ind₂_assoc' {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M')
    (h₄ : r + M' = N) {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁)
    (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃) :
    Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h₁) (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ (stdSum h₄) (extTensor π₁ (ind₂ (stdSum h₃) (extTensor π₂ π₃))))) := by
  subst h₁ h₃ h₂
  exact Stages.prod₂_assoc k r s t V₁ V₂ V₃ π₁ π₂ π₃ s₁ s₂ s₃

theorem multiProd_head {s : ℕ} {d : Fin (s + 1) → ℕ} {X : Fin (s + 1) → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) {T N : ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) (h : d 0 + T = N) (e' : (Σ a : Fin s, Fin (d a.succ)) ≃ Fin T) :
    Nonempty ((multiProd e π).Equiv
      (ind₂ (stdSum h) (extTensor (π 0) (multiProd e' fun a : Fin s => π a.succ)))) := by
  have hT : T = ∑ a : Fin s, d a.succ := by
    have := Fintype.card_congr e'
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this.symm
  subst hT h
  have A := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) d (Fin.sum_univ_succ d) π
  have B := multiProd_placing (k := k) e (stdBlocks d (Fin.sum_univ_succ d)) π
  have C := multiProd_placing (k := k) (stdBlocks (fun i : Fin s => d i.succ) rfl) e' fun a => π a.succ
  exact A.elim fun A => B.elim fun B => C.elim fun C =>
    ⟨B.trans (A.symm.trans (LocGL.prod₂Equiv (Representation.Equiv.refl (π 0)) C))⟩

theorem multiProd_empty {d d' : Fin 0 → ℕ} {X X' : Fin 0 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] [iX' : ∀ a, AddCommGroup (X' a)] [mX' : ∀ a, Module ℂ (X' a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d' a)) k) (X' a))
    {t : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin t) (e' : (Σ a, Fin (d' a)) ≃ Fin t) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π')) := by
  obtain rfl : d = d' := funext fun a => a.elim0
  obtain rfl : X = X' := funext fun a => a.elim0
  obtain rfl : iX = iX' := funext fun a => a.elim0
  obtain rfl : mX = mX' := funext fun a => a.elim0
  obtain rfl : π = π' := funext fun a => a.elim0
  exact multiProd_placing e e' π

theorem ind₂_unit_right {r t : ℕ} (h : r + t = r) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) {d : Fin 0 → ℕ} {X : Fin 0 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor π (multiProd e τ))).Equiv π) := by
  let f : (Σ _ : Fin 1, Fin r) ≃ Fin r :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  let e' : (Σ a : Fin 0, Fin r) ≃ Fin t :=
    (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin r) (Σ a, Fin (d a))).trans e
  have A := LocGL.nonempty_equiv_multiProd_one hπ f fun _ _ => rfl
  have B := multiProd_head (k := k) (d := fun _ : Fin 1 => r) (fun _ => π) f h e'
  have C := ind₂_congr h (eqv_refl π) (multiProd_empty (k := k) (fun a : Fin 0 => π) τ e' e)
  exact eqv_symm (eqv_trans A (eqv_trans B C))

theorem multiProd_comp_congr {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {f g : Fin u → Fin s} (hfg : f = g)
    {T : ℕ} (e : (Σ i, Fin (d (f i))) ≃ Fin T) (e' : (Σ i, Fin (d (g i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (f i)).π).Equiv (multiProd e' fun i => (σ (g i)).π)) := by
  subst hfg
  exact multiProd_placing e e' _

def sigmaPart {s s₁ s₂ : ℕ} (d : Fin s → ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s)
    (hb : Function.Bijective (Sum.elim ι₁ ι₂)) :
    (Σ a, Fin (d a)) ≃ (Σ i, Fin (d (ι₁ i))) ⊕ (Σ j, Fin (d (ι₂ j))) :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) (Equiv.ofBijective _ hb)).symm.trans
    (Equiv.sumSigmaDistrib fun x => Fin (d (Sum.elim ι₁ ι₂ x)))

def Commutes {p q : ℕ} (x : Irr k p) (y : Irr k q) : Prop :=
  ∀ (N : ℕ) (h₁ : p + q = N) (h₂ : q + p = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π y.π)).Equiv (ind₂ (stdSum h₂) (extTensor y.π x.π)))

theorem Commutes.symm {p q : ℕ} {x : Irr k p} {y : Irr k q} (h : Commutes x y) : Commutes y x :=
  fun N h₁ h₂ => (h N h₂ h₁).map Representation.Equiv.symm

end GlobalTheory.ProdReorder
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wToC_pow_comm {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p])
    (hσ : ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) :
    ∀ (k : ℕ) (x : FormalGroupSystem.WW p), (σ ^ k) (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, hσ, Function.iterate_succ_apply']

theorem dualOm_wToC : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) → ∀ (n' : ℕ), Even n' → ∀ B : OmBasis p n', GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) := by
  intro p _ σ hσ n' hn B
  have hk := wToC_pow_comm σ hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    exact Nat.two_mul_div_two_of_even hn
  · intro r
    exact ⟨Formalism.L2.G.Pend.wToC_mem_Wp p _, Formalism.L2.G.Pend.wToC_mem_Wp p _⟩
  · intro r
    refine ⟨?_, ?_⟩
    · rw [hk, B.fix r]
    · rw [hk, B.fixS r]
  · intro r r'
    have h := congrArg (Formalism.L2.G.Pend.wToC p) (B.dual r r')

    rw [map_sum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i => (σ ^ (2 * i)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r')))]
    simp only [← map_mul, hk]
    rw [h]
    split_ifs <;> simp

end GlobalTheory.TwU
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory

theorem atLin_adCoef_eq_stdSer : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), atLin (Formalism.L2.Ker.adCoef lam P P') (fun j => MvPowerSeries.X j) F = stdSer D lam (fun _ => 1) P P' F := by
  intro D p _ lam N N' P P' F
  unfold stdSer
  congr 1
  funext k j
  rw [one_mul]
  unfold Formalism.L2.Ker.adCoef chgB
  dsimp only
  split_ifs with h
  · rw [h]
  · rfl

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem _root_.GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  first | exact @GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | exact GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | (intros; apply GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wordNum_recWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordNum | exact GlobalTheory.HTW.Rec.recWord_wordNum | (intros; apply GlobalTheory.HTW.Rec.recWord_wordNum <;> assumption)
end
