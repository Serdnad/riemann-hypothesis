module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle067
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

def four : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (by norm_num)).trans finProdFinEquiv.symm

def posE (n n' : ℕ) : (Fin n' × Fin n) × Fin 4 ≃ Fin (n' * 2) × Fin (n * 2) :=
  ((Equiv.refl _).prodCongr four).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv))

abbrev Ix (D : D7) (n n' : ℕ) : Type := (Fin n' × Fin n) × (Fin 4 × D.what₂.Tau)

def blk (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) : Fin 4 × D.what₂.Tau → ℂ :=
  fun w => z w.2 (posE n n' (k, w.1)).1 (posE n n' (k, w.1)).2

def reix (D : D7) (n n' : ℕ) : TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun z p := blk D p.1 z p.2
  invFun y τ i j := y (((posE n n').symm (i, j)).1, (((posE n n').symm (i, j)).2, τ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext τ i j
    simp [blk]
  right_inv y := by
    funext p
    simp [blk]

def gBig {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    (Ix D n n' → ℂ) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun y p := B.gC (fun w => y (p.1, w)) p.2
  invFun y p := B.gC.symm (fun w => y (p.1, w)) p.2
  map_add' x y := by
    funext p
    show B.gC ((fun w => x (p.1, w)) + (fun w => y (p.1, w))) p.2 = _
    rw [map_add (f := _)]; rfl
  map_smul' c x := by
    funext p
    show B.gC (c • (fun w => x (p.1, w))) p.2 = _
    rw [map_smul]; rfl
  left_inv y := by
    funext p
    simp
  right_inv y := by
    funext p
    simp

def phi {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) :=
  (reix D n n').trans (gBig B n n')

theorem phi_apply {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) (p : Ix D n n') : phi B n n' z p = B.gC (blk D p.1 z) p.2 := rfl

def ixE (D : D7) (n n' : ℕ) : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) ≃ Ix D n n' :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    simp only [Fintype.card_prod, Fintype.card_fin, D.what₂.card_Tau, TaylorLogMetric.fF]
    ring)

def xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : Fin 4 → D.host.E :=
  B.γ₀.g.symm (Pi.single w 1)

def putB (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) :
    Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun i j => if ((posE n n').symm (i, j)).1 = k then x ((posE n n').symm (i, j)).2 else 0

def bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) → Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun j => putB D (ixE D n n' j).1 (xv B (ixE D n n' j).2)

def blkLat {ι m : Type} (Λ : AddSubgroup (m → ℂ)) : AddSubgroup (ι × m → ℂ) where
  carrier := {y | ∀ k, (fun w => y (k, w)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy k => Λ.add_mem (hx k) (hy k)
  neg_mem' := fun hx k => Λ.neg_mem (hx k)

end GlobalTheory.BaseVacuum
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabTan

theorem tanBasis_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  intro E _ _ _ H X X' t t' j m S T _ _ ψ x x' hx n v hv hv'
  have := t.semi.comm
  have := t'.semi.comm
  obtain ⟨k₁, k₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t ψ x n v hv hv'
  rw [← hx] at k₁ k₂
  have h₁ := isGrpPullback_pullback t'.G x'
  have hc := h₁.comp m.cart
  obtain ⟨a, b⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t (x' ≫ j) _ _ hc
  obtain ⟨-, b'⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t' x' _ _ h₁
  choose u hu using fun i => a _ (k₁ i)
  have hu' : ∀ i, (u i).left ≫ pullback.fst t'.G.hom x' ≫ m.φ = spMap (dualMap ψ) ≫ v i := hu
  have hb := (b n u).2 ⟨fun i => by rw [hu']; exact k₁ i, by rw [funext hu']; exact k₂⟩
  obtain ⟨c₁, c₂⟩ := (b' n u).1 hb
  exact ⟨fun i => (u i).left ≫ pullback.fst t'.G.hom x', fun i => by rw [Category.assoc]; exact hu' i, c₁, c₂⟩

end GlobalTheory.SabTan
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E]

theorem loc_eq_one_of_prod (ψ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ k : Eˣ, ∏ P ∈ S, ψ.locK P k = 1) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S)
    (x : (w.adicCompletion E)ˣ) : ψ.loc w x = 1 := by
  classical
  choose n hn using fun P => GlobalTheory.Mem.UnrAe.exists_levelLe ψ P
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E S w x (S.sup n + 1)
  have lev : ∀ P ∈ S, ∀ z : (P.adicCompletion E)ˣ,
      Valued.v ((z : P.adicCompletion E) - 1) ≤ WithZero.exp (-((S.sup n + 1 : ℕ) : ℤ)) → ψ.loc P z = 1 := by
    intro P hP z hz
    have h1 : Valued.v ((z : P.adicCompletion E) - 1) < Valued.v (1 : P.adicCompletion E) := by
      rw [map_one]
      refine lt_of_le_of_lt hz ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hu : IsUnitAt P z := by
      unfold IsUnitAt
      have e : (z : P.adicCompletion E) = ((z : P.adicCompletion E) - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ h1, map_one]
    refine hn P z hu (hz.trans ?_)
    rw [WithZero.exp_le_exp]
    have : n P ≤ S.sup n := Finset.le_sup hP
    omega
  have hS := h (Units.mk0 y hy0)
  rw [← Finset.mul_prod_erase S _ hw, Finset.prod_eq_one (fun P hP => ?_), mul_one] at hS
  · have e : ψ.loc w x = ψ.locK w (Units.mk0 y hy0) * (ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹))⁻¹ := by
      rw [map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc]; simp [HChar.locK]
    have h2 : ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹) = 1 := lev w hw _ (by
      have := hyw
      exact this)
    rw [e, hS, h2, inv_one, mul_one]
  · obtain ⟨hPw, hPS⟩ := Finset.mem_erase.1 hP
    refine lev P hPS _ ?_
    have h3 := hyv P hPS hPw
    show Valued.v (algebraMap E (P.adicCompletion E) y - 1) ≤ _
    rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub]
    first
      | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (y - 1)).trans_le h3
      | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h3)

end GlobalTheory.CMVal.InvConj

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjE_apply (x : E) : conjE x = IsCMField.complexConj E x := rfl

theorem conjE_symm_apply (x : E) : (conjE (E := E)).symm x = IsCMField.complexConj E x := by
  rw [RingEquiv.symm_apply_eq, conjE_apply, IsCMField.complexConj_apply_apply]

theorem under_plMap (j : E ≃+* E) (hj : ∀ x : maximalRealSubfield E, j (x : E) = x) (P : HeightOneSpectrum (𝓞 E)) :
    (plMap j P).under (OF E) = P.under (OF E) := by
  ext a
  have e : RingOfIntegers.mapRingEquiv j (algebraMap (OF E) (𝓞 E) a) = algebraMap (OF E) (𝓞 E) a :=
    RingOfIntegers.ext (hj (a : maximalRealSubfield E))
  show algebraMap (OF E) (𝓞 E) a ∈ (plMap j P).asIdeal ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal
  rw [← mem_plMap j P, e]

theorem mem_aboveF (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem prod_locK_conj (χ : HChar E) (hχ : TrivOnF χ) (v : HeightOneSpectrum (OF E)) (k : Eˣ) :
    ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (χ * transport conjE χ).locK P k = 1 := by
  have h1 : ∀ P, (χ * transport conjE χ).locK P k = χ.locK P k * (transport conjE χ).locK P k := fun P => rfl
  have hs : ∀ x : maximalRealSubfield E, (conjE (E := E)).symm (x : E) = x := fun x => by
    rw [conjE_symm_apply]; exact IsCMField.complexConj_apply_eq_self E x
  have hc : ∀ x : maximalRealSubfield E, (conjE (E := E)) (x : E) = x := fun x =>
    IsCMField.complexConj_apply_eq_self E x
  have h2 : ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (transport conjE χ).locK P k =
      ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, χ.locK P (Units.map (conjE (E := E)).toMonoidHom k) := by
    symm
    refine Finset.prod_nbij' (fun P => plMap (conjE (E := E)).symm P) (fun P => plMap conjE P) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hs P]; exact hP
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hc P]; exact hP
    · intro P _; exact plMap_plMap_symm conjE P
    · intro P _; exact plMap_symm_plMap conjE P
    · intro P _
      show χ.loc P (atFin P _) = (transport conjE χ).loc (plMap (conjE (E := E)).symm P) (atFin _ k)
      rw [transport_loc, locMap_atFin]
  rw [Finset.prod_congr rfl (fun P _ => h1 P), Finset.prod_mul_distrib, h2, ← Finset.prod_mul_distrib]
  have hN : (k : E) * conjE (k : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_mul, conjE_apply, IsCMField.complexConj_apply_apply, mul_comm]
  have hN0 : (⟨_, hN⟩ : maximalRealSubfield E) ≠ 0 := fun h0 =>
    mul_ne_zero k.ne_zero ((map_ne_zero _).2 k.ne_zero) (congrArg Subtype.val h0)
  have h3 := hχ.1 v (Units.mk0 _ hN0)
  unfold HChar.resFin at h3
  have hp : ∀ (s : Finset (HeightOneSpectrum (𝓞 E)))
      (f : HeightOneSpectrum (𝓞 E) → (maximalRealSubfield E)ˣ →* ℂˣ)
      (x : (maximalRealSubfield E)ˣ), (∏ P ∈ s, f P) x = ∏ P ∈ s, f P x := by
    intro s f x
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => simp only [Finset.prod_insert ha, MonoidHom.mul_apply, ih]
  rw [hp] at h3
  simp only [MonoidHom.comp_apply] at h3
  rw [← h3]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← map_mul]
  exact congrArg _ (Units.ext rfl)

theorem loc_transport (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    (transport conjE χ).loc P x = (χ.loc P x)⁻¹ := by
  have h := loc_eq_one_of_prod (χ * transport conjE χ) _ (prod_locK_conj χ hχ (P.under (OF E)))
    (w := P) ((mem_aboveF _ P).2 rfl) x
  change χ.loc P x * (transport conjE χ).loc P x = 1 at h
  exact eq_inv_of_mul_eq_one_right h

theorem unrAt_inv_iff (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) :
    χ⁻¹.UnrAt P ↔ χ.UnrAt (plMap conjE P) := by
  rw [← transport_unrAt_iff]
  unfold HChar.UnrAt
  change (∀ x, IsUnitAt P x → (χ.loc P x)⁻¹ = 1) ↔ _
  simp only [loc_transport χ hχ]

theorem val_inv_eq (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap conjE P)) :
    χ⁻¹.val P = χ.val (plMap conjE P) := by
  rw [← transport_val conjE χ P h]
  show (χ.loc P _)⁻¹ = (transport conjE χ).loc P _
  rw [loc_transport χ hχ]

theorem eulerFactor_inv (χ : HChar E) (hχ : TrivOnF χ) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    eulerFactor χ⁻¹ s P = eulerFactor χ s (plMap conjE P) := by
  unfold eulerFactor
  by_cases h : χ.UnrAt (plMap conjE P)
  · rw [if_pos ((unrAt_inv_iff χ hχ P).2 h), if_pos h, val_inv_eq χ hχ P h, absNorm_plMap]
  · rw [if_neg (fun h' => h ((unrAt_inv_iff χ hχ P).1 h')), if_neg h]

end GlobalTheory.CMVal.InvConj


open Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj in
theorem GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  intro E _ _ _ χ Λ hχ hL
  refine ⟨hL.1, fun s hs => ?_⟩
  let e : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
    ⟨plMap conjE, plMap (conjE (E := E)).symm, plMap_symm_plMap conjE, plMap_plMap_symm conjE⟩
  have he : eulerFactor χ⁻¹ s = eulerFactor χ s ∘ e := funext fun P => eulerFactor_inv χ hχ s P
  rw [he, Equiv.hasProd_iff]
  exact hL.2 s hs
end
end

section

noncomputable section

namespace GlobalTheory.HcIrr.Factor

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr Representation

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem tprod_update_injective (v : ∀ i, M i) (hv : ∀ i, v i ≠ 0) (i : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hw : ∀ j, Function.update v i x j ≠ 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hx0
    · rw [Function.update_of_ne hj]; exact hv j
  have hφ : ∀ j, ∃ φ : Module.Dual ℂ (M j), φ (Function.update v i x j) ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    exact hw j ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  choose φ hφ using hφ
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) hx
  rw [MultilinearMap.toLinearMap_apply, PiTensorProduct.lift.tprod, map_zero,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
  exact (Finset.prod_ne_zero_iff.2 fun j _ => hφ j) h1

end Tensor

section Blocks

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def blockIdx (b : Fin r → Fin s) (c : Fin s) : {i // b i = c} ≃ Block (natBlocks b) (c : ℕ) :=
  Equiv.subtypeEquivRight fun i => by simp [natBlocks, Fin.val_inj]

def blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) :
    {i // b i = c} ≃ Fin d :=
  (blockIdx b c).trans (monoEquivOfFin _ h).toEquiv.symm

theorem monoEquivOfFin_blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ}
    (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (x : {i // b i = c}) :
    ((monoEquivOfFin (Block (natBlocks b) (c : ℕ)) h (blockNum b c h x) : Block (natBlocks b) (c : ℕ)) : Fin r) = x.1 := by
  simp [blockNum, blockIdx]

theorem blockEmb_eq (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d)
    (g : GL (Fin d) K) :
    blockEmb (natBlocks b) (c : ℕ) h g = blockExt b c ((glEquiv K (blockNum b c h)).symm g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : b i = c ∧ b j = c
  · have h1 := blockEmb_in (natBlocks b) (c : ℕ) h g (blockNum b c h ⟨i, hij.1⟩) (blockNum b c h ⟨j, hij.2⟩)
    rw [monoEquivOfFin_blockNum, monoEquivOfFin_blockNum] at h1
    have h2 := blockExt_in b c ((glEquiv K (blockNum b c h)).symm g) ⟨i, hij.1⟩ ⟨j, hij.2⟩
    rw [h1, h2]
    rfl
  · have hn : ¬ (natBlocks b i = (c : ℕ) ∧ natBlocks b j = (c : ℕ)) := by
      simpa [natBlocks, Fin.val_inj] using hij
    rw [blockEmb_out (natBlocks b) (c : ℕ) h g i j hn, blockExt_out b c _ i j hij]

end Blocks

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem blockRes_leviTensor (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (g : GL (Fin d) K) :
    blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h g = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c
        ((lam c).ρ ((glEquiv K (blockNum b c h)).symm g))) := by
  show leviTensor b lam (blockEmb (natBlocks b) (c : ℕ) h g) = _
  rw [blockEmb_eq, leviTensor_blockExt]

theorem map_update_tprod {s : ℕ} {M : Fin s → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (c : Fin s) (A : M c →ₗ[ℂ] M c) (v : ∀ i, M i) (x : M c) :
    PiTensorProduct.map (Function.update (fun c' => (LinearMap.id : M c' →ₗ[ℂ] M c')) c A)
      (PiTensorProduct.tprod ℂ (Function.update v c x)) = PiTensorProduct.tprod ℂ (Function.update v c (A x)) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext c'
  by_cases hc : c' = c
  · subst hc; simp
  · simp [Function.update_of_ne hc]

theorem factor_iso : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ)
    (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ →
    ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)),
      ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  intro K _ _ _ r s b lam hsimp c d h W _ _ ρ hF
  refine ⟨blockNum b c h, ?_⟩
  set e := blockNum b c h
  let ρ' : Representation ℂ (GL (Fin d) K) (lam c) := (Formalism.IrreducibleCountingLemmas.TYPES.transp e (lam c)).ρ
  have hirr : ρ'.IsIrreducible := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (Formalism.L2.PT.simple_transp e (hsimp c))
  have hnt : ∀ c', Nontrivial (lam c') := fun c' =>
    PI.GreenLabelSurjWork.nontrivial_of_simple _ (hsimp c')
  choose v hv using fun c' => exists_ne (0 : (lam c' : Type))
  let f : IntertwiningMap ρ' (blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h) :=
    ((PiTensorProduct.tprod ℂ).toLinearMap v c).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => by
      rw [blockRes_leviTensor, MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply,
        map_update_tprod]
      rfl)
  have hinj : Function.Injective (IntertwiningMap.equivLinearMapAsModule ρ' _ f) :=
    tprod_update_injective v hv c
  have hiso := hF.2.of_injective _ hinj
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ').1 hirr
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) (⊤ : Submodule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule) :=
    IsSimpleModule.congr (Submodule.topEquiv)
  let E : ρ.asModule ≃ₗ[MonoidAlgebra ℂ (GL (Fin d) K)] ρ'.asModule := ((hiso ⊤).some.symm.trans Submodule.topEquiv)
  let F : IntertwiningMap ρ ρ' := (IntertwiningMap.equivLinearMapAsModule ρ ρ').symm E.toLinearMap
  refine ⟨LinearEquiv.ofBijective F.toLinearMap E.bijective, fun g x => ?_⟩
  exact IntertwiningMap.isIntertwining ρ ρ' F g x

end Main

end GlobalTheory.HcIrr.Factor
end
end

section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.finrank_commonFixed_le_one_of_commuting_hecke : ∀ (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V), (∀ c, e c * e c = e c) → (∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g)) → (∀ c c', c ≠ c' → Commute (e c) (e c')) → (∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h)) → (∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c) → (∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤) → ∀ W : Submodule ℂ V, (∀ v ∈ W, ∀ c, e c v = v) → finrank ℂ W ≤ 1 := by
  first | exact @GlobalTheory.CommutingHecke.finrank_fixed_le_one | exact GlobalTheory.CommutingHecke.finrank_fixed_le_one | (intros; apply GlobalTheory.CommutingHecke.finrank_fixed_le_one <;> assumption)
end
