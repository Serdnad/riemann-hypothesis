module

public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Pairing
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomologyMapPiLiftPiHomologyIsoHom
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle002
import GroundTheory.ProfiniteCohomology.Bundle001
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace LeibnizPairing

variable {LA LB LC : CochainComplex (ModuleCat.{u} k) ℕ} (μLL : LeibnizPairing LA LB LC)

noncomputable def shiftBoth : ∀ (r s m : ℕ), r + s = m + 1 →
    shiftNegOneX LA r → shiftNegOneX LB s → shiftNegOneX LC m
  | r + 1, s + 1, m + 1, _ => fun b c => μLL.μ (show r + s = m by omega) b c
  | _, _, _, _ => fun _ _ => 0

variable {KA KB KC LA' LB' : CochainComplex (ModuleCat.{u} k) ℕ} {fA : KA ⟶ LA} {fB : KB ⟶ LB}
  (ρA : KA ⟶ LA') (ρB : KB ⟶ LB') (μL : LeibnizPairing LA LB' LC) (μR : LeibnizPairing LA' LB LC)
  (hLL : ∀ {r s n : ℕ} (h : r + s = n) (u : LA.X r) (y : KB.X s),
    μL.μ h u ((ρB.f s).hom y) = μLL.μ h u ((fB.f s).hom y))
  (hRR : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (w : LB.X s),
    μR.μ h ((ρA.f r).hom x) w = μLL.μ h ((fA.f r).hom x) w)

include hLL hRR in
theorem shiftLeft_sub_shiftRight {r s m : ℕ} (h : r + s = m + 1) (x : KA.X r)
    (b : shiftNegOneX LA r) (y : KB.X s) (c : shiftNegOneX LB s)
    (hx : shiftNegOneSucc LA r ((fA.f r).hom x) + (shiftNegOneD LA r).hom b = 0)
    (hy : shiftNegOneSucc LB s ((fB.f s).hom y) + (shiftNegOneD LB s).hom c = 0) :
    μL.shiftLeft r s (m + 1) h b ((ρB.f s).hom y) -
        (-1 : k) ^ r • μR.shiftRight r s (m + 1) h ((ρA.f r).hom x) c =
      (shiftNegOneD LC m).hom ((-1 : k) ^ r • μLL.shiftBoth r s m h b c) := by
  cases r with
  | zero =>
    have hx' : (fA.f 0).hom x = 0 := by
      have e : (shiftNegOneD LA 0).hom b = 0 := rfl
      rw [e, add_zero] at hx
      exact hx
    have e1 : μL.shiftLeft 0 s (m + 1) h b ((ρB.f s).hom y) = 0 := rfl
    have e2 : μLL.shiftBoth 0 s m h b c = 0 := rfl
    rw [e1, e2, smul_zero, map_zero, zero_sub, neg_eq_zero]
    clear e1 e2 hy
    cases s with
    | zero =>
      have e : μR.shiftRight 0 0 (m + 1) h = 0 := rfl
      rw [e, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
    | succ s =>
      revert c
      intro (c : LB.X s)
      change (-1 : k) ^ 0 • μR.μ (show 0 + s = m by omega) ((ρA.f 0).hom x) c = 0
      rw [hRR, hx', map_zero, LinearMap.zero_apply, smul_zero]
  | succ r =>
    cases s with
    | zero =>
      have hy' : (fB.f 0).hom y = 0 := by
        have e : (shiftNegOneD LB 0).hom c = 0 := rfl
        rw [e, add_zero] at hy
        exact hy
      have e1 : μR.shiftRight (r + 1) 0 (m + 1) h ((ρA.f (r + 1)).hom x) c = 0 := rfl
      have e2 : μLL.shiftBoth (r + 1) 0 m h b c = 0 := rfl
      rw [e1, e2, smul_zero, smul_zero, map_zero, sub_zero]
      clear e1 e2 hx
      revert b
      intro (b : LA.X r)
      change μL.μ (show r + 0 = m by omega) b ((ρB.f 0).hom y) = 0
      rw [hLL, hy', map_zero]
    | succ s =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨r + s, by omega⟩
      revert b hx c hy
      intro (b : LA.X r) hx (c : LB.X s) hy
      have hx' : (fA.f (r + 1)).hom x = (LA.d r (r + 1)).hom b := by
        have e : ((fA.f (r + 1)).hom x : LA.X (r + 1)) + -(LA.d r (r + 1)).hom b = 0 := hx
        exact add_neg_eq_zero.1 e
      have hy' : (fB.f (s + 1)).hom y = (LB.d s (s + 1)).hom c := by
        have e : ((fB.f (s + 1)).hom y : LB.X (s + 1)) + -(LB.d s (s + 1)).hom c = 0 := hy
        exact add_neg_eq_zero.1 e
      change μL.μ (show r + (s + 1) = m + 1 by omega) b ((ρB.f (s + 1)).hom y) -
          (-1 : k) ^ (r + 1) • μR.μ (show r + 1 + s = m + 1 by omega) ((ρA.f (r + 1)).hom x) c =
        -(LC.d m (m + 1)).hom ((-1 : k) ^ (r + 1) • μLL.μ (show r + s = m by omega) b c)
      have e2 : (-1 : k) ^ (r + 1) * (-1 : k) ^ r = -1 := by
        rw [← pow_add, show r + 1 + r = 2 * r + 1 by omega, pow_succ, pow_mul, neg_one_sq, one_pow,
          one_mul]
      rw [hLL, hRR, hx', hy', map_smul, μLL.leibniz, smul_add, smul_smul, e2, neg_one_smul,
        neg_add, neg_neg]
      abel

variable {fC : KC ⟶ LC} (μK : LeibnizPairing KA KB KC)
  (hL : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (y : KB.X s),
    (fC.f n).hom (μK.μ h x y) = μL.μ h ((fA.f r).hom x) ((ρB.f s).hom y))
  (hR : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (y : KB.X s),
    (fC.f n).hom (μK.μ h x y) = μR.μ h ((ρA.f r).hom x) ((fB.f s).hom y))

include hLL hRR in
theorem coconeLeftμ_sub_coconeRightμ_eq_d {r s m : ℕ} (h : r + s = m + 1)
    (X : (mappingCoconeNat fA).X r) (Y : (mappingCoconeNat fB).X s)
    (hX : (mappingCoconeNatD fA r).hom X = 0) (hY : (mappingCoconeNatD fB s).hom Y = 0) :
    ∃ W : (mappingCoconeNat fC).X m,
      coconeLeftμ μL ρB μK (f := fA) (f' := fC) h X (((mappingCoconeNat.fst fB).f s).hom Y) -
        coconeRightμ μR ρA μK (f := fB) (f' := fC) h (((mappingCoconeNat.fst fA).f r).hom X) Y =
      (mappingCoconeNatD fC m).hom W := by
  obtain ⟨x0, b⟩ := X
  obtain ⟨y0, c⟩ := Y
  refine ⟨((0 : KC.X m), (-1 : k) ^ r • μLL.shiftBoth r s m h b c), Prod.ext ?_ ?_⟩
  · change μK.μ h x0 y0 - μK.μ h x0 y0 = (KC.d m (m + 1)).hom 0
    rw [sub_self, map_zero]
  · change μL.shiftLeft r s (m + 1) h b ((ρB.f s).hom y0) -
        (-1 : k) ^ r • μR.shiftRight r s (m + 1) h ((ρA.f r).hom x0) c =
      shiftNegOneSucc LC m ((fC.f m).hom 0) +
        (shiftNegOneD LC m).hom ((-1 : k) ^ r • μLL.shiftBoth r s m h b c)
    rw [map_zero, map_zero, zero_add]
    exact shiftLeft_sub_shiftRight μLL ρA ρB μL μR hLL hRR h x0 b y0 c (congrArg Prod.snd hX)
      (congrArg Prod.snd hY)


include hLL hRR in
theorem coconeLeft_homology_eq_coconeRight_homology {r s n : ℕ} (h : r + s = n)
    (x : (mappingCoconeNat fA).homology r) (y : (mappingCoconeNat fB).homology s) :
    (coconeLeft μL ρB μK hL).homology h x
        ((HomologicalComplex.homologyMap (mappingCoconeNat.fst fB) s).hom y) =
      (coconeRight μR ρA μK hR).homology h
        ((HomologicalComplex.homologyMap (mappingCoconeNat.fst fA) r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, homology_homologyπ,
    homology_homologyπ]
  rw [← sub_eq_zero, ← map_sub]
  cases n with
  | zero =>
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := ⟨by omega, by omega⟩
    have e : (coconeLeft μL ρB μK hL).cycles h x
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fB) 0).hom y) -
      (coconeRight μR ρA μK hR).cycles h
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fA) 0).hom x) y = 0 := by
      apply iCycles_hom_injective
      rw [map_sub, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
        iCycles_cyclesMap_apply, map_zero, sub_eq_zero]
      exact Prod.ext rfl rfl
    rw [e, map_zero]
  | succ m =>
    have hX := iCycles_d_apply (mappingCoconeNat fA) r (r + 1) x
    have hY := iCycles_d_apply (mappingCoconeNat fB) s (s + 1) y
    rw [mappingCoconeNat_d] at hX hY
    obtain ⟨W, hW⟩ := coconeLeftμ_sub_coconeRightμ_eq_d μLL ρA ρB μL μR hLL hRR μK h _ _ hX hY
    have e : (coconeLeft μL ρB μK hL).cycles h x
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fB) s).hom y) -
      (coconeRight μR ρA μK hR).cycles h
        ((HomologicalComplex.cyclesMap (mappingCoconeNat.fst fA) r).hom x) y =
        ((mappingCoconeNat fC).toCycles m (m + 1)).hom W := by
      apply iCycles_hom_injective
      rw [map_sub, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
        iCycles_cyclesMap_apply, iCycles_toCycles_hom_apply, mappingCoconeNat_d]
      exact hW
    rw [e, homologyπ_toCycles_hom_apply]

end LeibnizPairing

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

section Global

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

noncomputable def cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    (cochainsComplex A).X r →ₗ[k] (cochainsComplex B).X s →ₗ[k] (cochainsComplex C).X n :=
  (cupLocallyConstant h).compr₂ ((cochainsMap μ).f n).hom

theorem cochainOf_cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (x : (cochainsComplex A).X r) (y : (cochainsComplex B).X s) :
    cochainOf (A := C) (cupPairingCochains μ h x y) =
      fun σ => μ.hom (cupCochain h (cochainOf (A := A) x) (cochainOf (A := B) y) σ) :=
  rfl

theorem d_cupLocallyConstant {r s n : ℕ} (h : r + s = n) (x : (cochainsComplex A).X r)
    (y : (cochainsComplex B).X s) :
    ((cochainsComplex (A ⊗ B)).d n (n + 1)).hom (cupLocallyConstant h x y) =
      cupLocallyConstant (by omega) (((cochainsComplex A).d r (r + 1)).hom x) y +
        (-1 : k) ^ r • cupLocallyConstant (by omega) x (((cochainsComplex B).d s (s + 1)).hom y) := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_smul]
  exact (cochainOf_d _).trans ((d_cupCochain h _ _).trans (by
    rw [← cochainOf_d, ← cochainOf_d]
    rfl))

noncomputable def cupLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (cochainsComplex A) (cochainsComplex B) (cochainsComplex C) where
  μ h := cupPairingCochains μ h
  leibniz {r s n} h x y := by
    change ((cochainsComplex C).d n (n + 1)).hom
        (((cochainsMap μ).f n).hom (cupLocallyConstant h x y)) =
      ((cochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) (((cochainsComplex A).d r (r + 1)).hom x) y) +
        (-1 : k) ^ r • ((cochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) x (((cochainsComplex B).d s (s + 1)).hom y))
    rw [hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap μ).comm n (n + 1)),
      d_cupLocallyConstant, map_add, map_smul]

theorem cupLeibniz_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) (x : cohomology A r)
    (y : cohomology B s) : (cupLeibniz μ).homology h x y = cupPairing μ h x y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  refine ((cupLeibniz μ).homology_homologyπ h x y).trans ?_
  refine Eq.trans ?_ (cupPairing_cohomologyπ μ h x y).symm
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply]
  exact congrArg ((cochainsMap μ).f n).hom (cocycleι_cupCocycles h x y).symm

end Global

namespace LeibnizPairing

variable {k : Type u} [CommRing k] {ι : Type u} {K N P : ι → CochainComplex (ModuleCat.{u} k) ℕ}
  (μs : ∀ v, LeibnizPairing (K v) (N v) (P v))

noncomputable def pi : LeibnizPairing (piComplex K) (piComplex N) (piComplex P) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : ∀ v, (K v).X r) (y : ∀ v, (N v).X s) =>
      (show (piComplex P).X n from fun v => (μs v).μ h (x v) (y v)))
    (fun x x' y => funext fun v => LinearMap.map_add₂ _ _ _ _)
    (fun c x y => funext fun v => LinearMap.map_smul₂ _ _ _ _)
    (fun x y y' => funext fun v => map_add _ _ _)
    (fun c x y => funext fun v => map_smul _ _ _)
  leibniz {r s n} h x y := funext fun v => by
    rw [piComplex_d_hom_apply]
    change ((P v).d n (n + 1)).hom ((μs v).μ h (x v) (y v)) =
      (μs v).μ (by omega) (((piComplex K).d r (r + 1)).hom x v) (y v) +
        (-1 : k) ^ r • (μs v).μ (by omega) (x v) (((piComplex N).d s (s + 1)).hom y v)
    rw [piComplex_d_hom_apply, piComplex_d_hom_apply]
    exact (μs v).leibniz h (x v) (y v)

theorem piHomologyIso_hom_pi_homology {r s n : ℕ} (h : r + s = n)
    (x : (piComplex K).homology r) (y : (piComplex N).homology s) (v : ι) :
    (piHomologyIso P n).hom.hom ((pi μs).homology h x y) v =
      (μs v).homology h ((piHomologyIso K r).hom.hom x v) ((piHomologyIso N s).hom.hom y v) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [piHomologyIso_hom_apply, piHomologyIso_hom_apply, piHomologyIso_hom_apply,
    homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
    iCycles_cyclesMap_apply]
  rfl

end LeibnizPairing

section Local

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  [∀ v, IsDiscreteRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

theorem localRes_cupPairingCochains (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (b v) ≫ μᵥ v)
    {r s n : ℕ} (h : r + s = n) (x : (cochainsComplex A).X r) (z : (cochainsComplex B).X s) :
    ((localRes φ C Cᵥ c).f n).hom (cupPairingCochains μ h x z) =
      (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f r).hom x)
        (((localRes φ B Bᵥ b).f s).hom z) := by
  funext v
  apply cochainOf_injective
  funext σ
  change (c v).hom (μ.hom (cupCochain h (cochainOf (A := A) x) (cochainOf (A := B) z)
      (⇑(φ v).toMonoidHom ∘ σ))) =
    (μᵥ v).hom (cupCochain h (fun τ => (a v).hom (cochainOf (A := A) x (⇑(φ v).toMonoidHom ∘ τ)))
      (fun τ => (b v).hom (cochainOf (A := B) z (⇑(φ v).toMonoidHom ∘ τ))) σ)
  rw [cupCochain_apply, cupCochain_apply, ← Rep.hom_comm_apply, partialProd_comp_monoidHom]
  exact congrArg (fun F : Rep.res (φ v).toMonoidHom (A ⊗ B) ⟶ Cᵥ v => F.hom
    ((cochainOf (A := A) x fun i => (⇑(φ v).toMonoidHom ∘ σ) ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ ((φ v).toMonoidHom (Fin.partialProd σ ⟨r, by omega⟩))
        (cochainOf (A := B) z fun j => (⇑(φ v).toMonoidHom ∘ σ) ⟨r + j, by omega⟩) :
      (A ⊗ B : Rep k G))) (hμ v)

end Local

end GroundTheory.ProfCoh
end
