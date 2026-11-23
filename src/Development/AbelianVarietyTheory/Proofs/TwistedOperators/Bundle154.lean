module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

def sumMap (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) →ₗ[D.host.E] Y.V :=
  ι.coprod ((Fintype.linearCombination D.host.E z).coprod
    ((Fintype.linearCombination D.host.E e).coprod (Fintype.linearCombination D.host.E f)))

theorem sumMap_apply (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (p : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    sumMap Y X ι z e f p = ι p.1 + (∑ i, p.2.1 i • z i + (∑ i, p.2.2.1 i • e i + ∑ i, p.2.2.2 i • f i)) := by
  simp [sumMap, Fintype.linearCombination_apply]

theorem hT_swap (Y : HSp D) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

theorem form_sumMap {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f)
    (p q : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    Y.hT (sumMap Y X ι z e f p) (sumMap Y X ι z e f q) =
      X.hT p.1 q.1 + (∑ i, star (p.2.1 i) * q.2.1 i * c +
        (∑ i, star (p.2.2.1 i) * q.2.2.2 i + ∑ i, star (p.2.2.2 i) * q.2.2.1 i)) := by
  have hsub : Subsingleton (Fin a) := by
    have := h.a_le
    exact ⟨fun i j => Fin.ext (by omega)⟩
  have zz : ∀ i j, Y.hT (z i) (z j) = if i = j then c else 0 := fun i j => by
    obtain rfl := Subsingleton.elim i j
    rw [if_pos rfl]; exact h.z_norm i
  have zx : ∀ i x, Y.hT (z i) (ι x) = 0 := fun i x => h.z_X i x
  have xz : ∀ i x, Y.hT (ι x) (z i) = 0 := fun i x => by rw [hT_swap, zx, star_zero]
  have ex : ∀ i x, Y.hT (e i) (ι x) = 0 := fun i x => (h.hyp_X i x).1
  have xe : ∀ i x, Y.hT (ι x) (e i) = 0 := fun i x => by rw [hT_swap, ex, star_zero]
  have fx : ∀ i x, Y.hT (f i) (ι x) = 0 := fun i x => (h.hyp_X i x).2
  have xf : ∀ i x, Y.hT (ι x) (f i) = 0 := fun i x => by rw [hT_swap, fx, star_zero]
  have ez : ∀ i j, Y.hT (e i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).1
  have ze : ∀ i j, Y.hT (z j) (e i) = 0 := fun i x => by rw [hT_swap, ez, star_zero]
  have fz : ∀ i j, Y.hT (f i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).2
  have zf : ∀ i j, Y.hT (z j) (f i) = 0 := fun i x => by rw [hT_swap, fz, star_zero]
  have ee : ∀ i j, Y.hT (e i) (e j) = 0 := fun i j => h.ee j i
  have ff : ∀ i j, Y.hT (f i) (f j) = 0 := fun i j => h.ff j i
  have fe : ∀ i j, Y.hT (f i) (e j) = if j = i then 1 else 0 := fun i j => h.ef j i
  have ef : ∀ i j, Y.hT (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hT_swap, fe]; split_ifs <;> simp
  have xx : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := h.isom
  rw [sumMap_apply, sumMap_apply]

  simp only [map_add (f := _), map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
  LinearMap.smul_apply, zz, zx, xz, ex, xe, fx, xf, ez, ze, fz, zf, ee, ff, fe, ef, xx, smul_eq_mul, mul_zero,
  Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
  if_true, mul_one, RingHom.id_apply, starRingEnd_apply]
  rw [add_comm (∑ i, star (p.2.2.1 i) * q.2.2.2 i)]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem sumMap_injective {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) : Function.Injective (sumMap Y X ι z e f) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨x, α, β, γ⟩ hp
  have H := fun q => form_sumMap h (x, α, β, γ) q
  simp only [hp, map_zero, LinearMap.zero_apply] at H
  have h1 : x = 0 := X.nondeg.1 x fun y => by simpa using (H (y, 0, 0, 0)).symm
  have h2 : α = 0 := funext fun i => by
    simpa [Pi.single_apply, hc] using (H (0, Pi.single i 1, 0, 0)).symm
  have h3 : β = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, 0, Pi.single i 1)).symm
  have h4 : γ = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, Pi.single i 1, 0)).symm
  simp [h1, h2, h3, h4]

def sumEquiv {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) ≃ₗ[D.host.E] Y.V :=
  LinearEquiv.ofInjectiveOfFinrankEq (sumMap Y X ι z e f) (sumMap_injective h hc) (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, X.rank_eq, Y.rank_eq, h.rank]
    ring)

theorem sumEquiv_apply {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) (p) :
    sumEquiv h hc p = sumMap Y X ι z e f p := rfl

theorem exists_isom {Y Y' X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {ι' : X.V →ₗ[D.host.E] Y'.V} {a ρ : ℕ}
    {z : Fin a → Y.V} {z' : Fin a → Y'.V} {c : D.host.E} {e f : Fin ρ → Y.V} {e' f' : Fin ρ → Y'.V}
    (h : IsDec Y X ι z c e f) (h' : IsDec Y' X ι' z' c e' f') (hc : c ≠ 0) :
    ∃ io : Y.V ≃ₗ[D.host.E] Y'.V, HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' x) ∧ (∀ i, io (z i) = z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i := by
  have key : ∀ p, ((sumEquiv h hc).symm.trans (sumEquiv h' hc)) (sumMap Y X ι z e f p) =
      sumMap Y' X ι' z' e' f' p := fun p => by
    rw [← sumEquiv_apply h hc, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sumEquiv_apply]
  refine ⟨(sumEquiv h hc).symm.trans (sumEquiv h' hc), fun x y => ?_, fun x => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨p, rfl⟩ := (sumEquiv h hc).surjective x
    obtain ⟨q, rfl⟩ := (sumEquiv h hc).surjective y
    rw [sumEquiv_apply, sumEquiv_apply, LinearEquiv.coe_coe, key, key, form_sumMap h, form_sumMap h']
  · simpa [sumMap_apply] using key (x, 0, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, Pi.single i 1, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, Pi.single i 1, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, 0, Pi.single i 1)

theorem isDec_rescale {Y X X' : HSp D} {ι : X'.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X' ι z c e f) (φ : X.V →ₗ[D.host.E] X'.V) (hφ : HSpace.IsIsomEmb X X' φ)
    (hr : X.rank = X'.rank) (π : D.host.E) :
    IsDec Y X (ι ∘ₗ φ) (fun i => π • z i) (c * (π * star π)) e f := by
  refine
    { isom := fun x y => (h.isom _ _).trans (hφ x y)
      a_le := h.a_le
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := h.ee
      ff := h.ff
      ef := h.ef
      hyp_X := fun i x => h.hyp_X i (φ x)
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [hr, h.rank]
  · intro i
    have := h.z_norm i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at this ⊢
    rw [this]
    ring
  · intro i x
    have := h.z_X i (φ x)
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at this ⊢
    rw [this, mul_zero]
  · intro i j
    have := h.hyperbolicDecomp_hyp_orthogonal_line i j
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, smul_eq_mul] at this ⊢
    rw [this.1, this.2, mul_zero]
    exact ⟨rfl, rfl⟩

theorem stdIsomSt_of_rationalSt : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  intro D hR u
  refine ⟨?_, ?_⟩
  · obtain ⟨π, h1, h2, -⟩ := D.T_norm u
    exact ⟨π, h1, by rw [bridge_star_holds D.R D.host]; exact h2⟩
  intro π hπ s a ρ Y X ι z e f Y' X' ι' z' e' f' h h' hX hX' hp hp' hr
  obtain ⟨φ, hφ⟩ := hR X X' hX hX' hr fun τ => by rw [hp τ, hp' τ, hr]
  have h2 := isDec_rescale h' φ.toLinearMap hφ hr (π : D.host.E)
  rw [hπ.2] at h2
  have hc : ((s : ℤ) : D.host.E) * Tu D u ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr s.ne_zero) (Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero)
  obtain ⟨io, a1, a2, a3, a4⟩ := exists_isom h h2 hc
  exact ⟨φ, io, hφ, a1, a2, a3, a4⟩

end GlobalTheory.StdIsom
end
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem nonempty_invFun_dual_tprod_equiv (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  let L : σ.IntertwiningMap ρ →ₗ[ℂ] invFun (ρ.dual.tprod σ) :=
    { toFun := fun f => ⟨TensorProduct.lift (LinearMap.lcomp ℂ ℂ f.toLinearMap), fun g x => by
        induction x with
        | tmul ξ w =>
          have h := LinearMap.congr_fun (f.isIntertwining' g) w
          simp only [LinearMap.comp_apply] at h
          simp only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
            LinearMap.lcomp_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, h,
            Representation.inv_self_apply]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]⟩
      map_add' := fun f f' => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (f.toLinearMap w + f'.toLinearMap w) = ξ (f.toLinearMap w) + ξ (f'.toLinearMap w)
        exact map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (c • f.toLinearMap w) = c • ξ (f.toLinearMap w)
        exact map_smul _ _ _) }
  have hL : ∀ f ξ w, (L f).1 (ξ ⊗ₜ w) = ξ (f.toLinearMap w) := fun _ _ _ => rfl
  refine ⟨(LinearEquiv.ofBijective L ⟨fun f f' h => ?_, fun l => ?_⟩).symm⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ _ = ξ _
    rw [← hL, ← hL, h]
  · let φ : W →ₗ[ℂ] V := (Module.evalEquiv ℂ V).symm.toLinearMap ∘ₗ (TensorProduct.curry l.1).flip
    have hφ : ∀ (ξ : Module.Dual ℂ V) w, ξ (φ w) = l.1 (ξ ⊗ₜ w) := fun ξ w => by
      simp [φ]
    refine ⟨⟨φ, fun g => LinearMap.ext fun w => ?_⟩, Subtype.ext (TensorProduct.ext' fun ξ w => hφ ξ w)⟩
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ (φ (σ g w)) = (ξ ∘ₗ ρ g) (φ w)
    rw [hφ, hφ, ← mem_invFun.1 l.2 g ((ξ ∘ₗ ρ g) ⊗ₜ w), Representation.tprod_apply, TensorProduct.map_tmul]
    congr 2
    ext v
    simp [Module.Dual.transpose_apply]

end GlobalTheory.OneFunctional
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix GlobalTheory.AdelicLatMove
open scoped TensorProduct




noncomputable section

namespace GlobalTheory.LatStab

variable {D : D7}

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  ext i j
  rfl

theorem mulVec_mem_of_mem_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (x : Fin n → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hM
  rw [hβ _]
  have hx' := (hβ x).1 hx
  have e : (β⁻¹).val * (frGL β y).val = (intGL D.host.F D.host.E n y).val * (β⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    change β⁻¹ * (β * intGL D.host.F D.host.E n y * β⁻¹) = _
    group
  intro i
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  change ∑ j, (intGL D.host.F D.host.E n y).val i j * ((β⁻¹).val *ᵥ x) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (y.val i j).2 (hx' j)

theorem rankOne_smul_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    (γ : Af D.host.F) (hγ : γ ∈ Formalism.UG.intAd D.host.F) (hP : ∀ v, ¬ Pv v → evalV D.host.F v γ = 0)
    (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → Lev.EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → Lev.EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • t) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s _ ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      have e : (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • fun i => (y i ⊗ₜ[D.host.F] β : Lev.EAf D)) =
          fun i => y i ⊗ₜ[D.host.F] (γ * β) := by
        ext i
        simp
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨γ * β * α, (mul_mem (mul_mem hγ hβ) hα : γ * β * α ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_,
        a, ha, x, hx, y, hy, rankOne_pure S T a x y α (γ * β)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [smul_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add, map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := rankOneHom S T a), AddMonoidHom.add_apply]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (g : GA D S) (h : GA D T)
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : (fun i => (t i ⊗ₜ[D.host.F] α : Lev.EAf D)) =
        ((1 : D.host.E) ⊗ₜ[D.host.F] α : Lev.EAf D) • fun i => (t i ⊗ₜ[D.host.F] (1 : Af D.host.F) : Lev.EAf D) := by
      ext i
      simp
    rw [← e, actO_rankOne, e2, Matrix.mulVec_smul, ← finE_val, ← finE_val]
    exact rankOne_smul_mem_latO S T ΛS ΛT Pv α hα hP a ha _
      (mulVec_mem_of_mem_St ΛS βS _ hS hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_of_mem_St ΛT βT _ hT hh _ (pure_mem_hatL ΛT 1 (one_mem _) t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh Pv u
  refine ⟨actO_mem S T ΛS ΛT βS βT hS hT g h hg hh Pv u, fun hu => ?_⟩
  have h1 := actO_mem S T ΛS ΛT βS βT hS hT g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg)
    (by rw [map_inv]; exact inv_mem hh) Pv _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LatStab

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCharExp

theorem exists_zpow_of_trivial (ψ : ℂˣ →* Circle) (hc : Continuous ψ)
    (h : ∀ s : ℂˣ, starRingEnd ℂ (s : ℂ) = s → ψ (s * s) = 1) :
    ∃ k : ℤ, ∀ z : ℂˣ, ((ψ z : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by
  have hu : Continuous (Circle.toUnits : Circle →* ℂˣ) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact (continuous_subtype_val.comp (continuous_inv (G := Circle))).congr fun u => by simp [Function.comp, Circle.coe_inv]
  obtain ⟨k, hk⟩ := GlobalTheory.circle_hom_eq_zpow (ψ.comp Circle.toUnits) (hc.comp hu)
  refine ⟨k, fun z => ?_⟩
  have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  have h1 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs : ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    simp [Submonoid.unitSphere, h0.ne']⟩
  have hu' : (u : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
  have e : z = Circle.toUnits u * (Units.mk0 _ hs * Units.mk0 _ hs) := by
    apply Units.ext
    show (z : ℂ) = (u : ℂ) * (((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) * ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ))
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0.le, hu', div_mul_cancel₀ _ h1]
  have e2 : ψ z = u ^ k := by
    rw [e, map_mul, h _ (Complex.conj_ofReal _), mul_one]
    exact hk u
  rw [e2, ← hu', Circle.coe_zpow]

variable {D : D7} {θ : InfFam D}

theorem ext_of_chart {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {a b : AE D}
    (h1 : finPart D a = finPart D b) (h2 : ∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) : a = b := by
  rw [← sub_eq_zero]
  refine h.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => ?_
  rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

theorem exists_real_hom {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) :
    ∃ e : (D.what₂.Tau → ℂ) →* AE D, Continuous e ∧ (∀ z, finPart D (e z) = 1) ∧
      ∀ z τ, θ τ (infPart D (e z)) = z τ := by
  have a1 : ∀ z, finPart D (1 + σ (z - 1)) = 1 := fun z => by rw [RingHom.map_add (f := _), h.fin, add_zero, RingHom.map_one]
  have a2 : ∀ z τ, θ τ (infPart D (1 + σ (z - 1))) = z τ := fun z τ => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), h.comp, RingHom.map_one, RingHom.map_one]; simp
  refine ⟨{ toFun := fun z => 1 + σ (z - 1)
            map_one' := by rw [sub_self, σ.map_zero, add_zero]
            map_mul' := fun z w => ext_of_chart h (by rw [RingHom.map_mul, a1, a1, a1, mul_one]) fun τ => by
              rw [RingHom.map_mul, RingHom.map_mul, a2, a2, a2, Pi.mul_apply] }, ?_, a1, a2⟩
  exact continuous_const.add (h.cont.comp (continuous_id.sub continuous_const))

theorem map_sq_eq_one {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (y : (AE D)ˣ)
    (hy : cA D (y : AE D) = y) : χ (y * y) = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := hχ
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
  have e : idF D (GlobalTheory.VolHeckeCompare.normU D y) = y * y := by
    refine (hN y).trans (Units.ext ?_)
    show (y : AE D) * cA D (y : AE D) = (y : AE D) * y
    rw [hy]
  rw [← e, h η hη, hη.2.2.1 y, one_pow]

theorem exists_hasInfExp : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau),
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  intro D θ χ n τ hθ hχ hr
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, ec, e1, e2⟩ := exists_real_hom h
  let f : ℂ →* AE D := e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have fc : Continuous f := ec.comp (continuous_mulSingle (A := fun _ : D.what₂.Tau => ℂ) τ)
  have f1 : ∀ z, finPart D (f z) = 1 := fun z => e1 _
  have f2 : ∀ z τ', θ τ' (infPart D (f z)) = (Pi.mulSingle τ z : D.what₂.Tau → ℂ) τ' := fun z τ' => e2 _ τ'
  obtain ⟨k, hk⟩ := exists_zpow_of_trivial (χ.comp (Units.map f)) (hχ.1.comp (fc.units_map f)) fun s hs => by
    rw [MonoidHom.comp_apply, MonoidHom.map_mul]
    refine map_sq_eq_one hr _ (ext_of_chart h ?_ fun τ' => ?_)
    · have e3 : finPart D (cA D (f s)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (f s)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (f s)
      show finPart D (cA D (f s)) = finPart D (f s)
      rw [e3, f1, RingHom.map_one]
    · show θ τ' (infPart D (cA D (f s))) = θ τ' (infPart D (f s))
      rw [GlobalTheory.FockCompare.comp_cA hθ, f2]
      by_cases ht : τ' = τ
      · rw [ht, Pi.mulSingle_eq_same, hs]
      · rw [Pi.mulSingle_eq_of_ne ht, RingHom.map_one]
  refine ⟨(k : ℚ) / 2, k, by ring, ⟨θ, hθ⟩, fun θ' hθ' x x1 x2 => ?_⟩
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  let z : ℂˣ := Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  have hz : (z : ℂ) = θ τ (infPart D (x : AE D)) := rfl
  have ex : Units.map f z = x := by
    refine Units.ext (ext_of_chart h ((f1 z).trans x1.symm) fun τ' => (f2 z τ').trans ?_)
    by_cases ht : τ' = τ
    · rw [ht, Pi.mulSingle_eq_same, hz]
    · rw [Pi.mulSingle_eq_of_ne ht, x2 τ' ht]
  have := hk z
  rwa [MonoidHom.comp_apply, ex, hz] at this

end GlobalTheory.SplitCharExp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_iff_pullback_matrix : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  first | exact @GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | exact GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | (intros; apply GlobalTheory.HalfCoordSB.isSBHalf_iff_pull <;> assumption)
end
