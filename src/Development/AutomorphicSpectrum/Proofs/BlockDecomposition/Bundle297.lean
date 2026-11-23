module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import Mathlib.Data.Fin.Tuple.Sort
public import GroundTheory.AutomorphicForms.Satake
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def firstEmb (d : Fin 2 → ℕ) : GL (Fin (d 0)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 0

def secondEmb (d : Fin 2 → ℕ) : GL (Fin (d 1)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 1

theorem firstEmb_comm (d : Fin 2 → ℕ) (g : GL (Fin (d 0)) k) (h : GL (Fin (d 1)) k) :
    firstEmb d g * secondEmb d h = secondEmb d h * firstEmb d g :=
  Pi.mulSingle_commute (f := fun a => GL (Fin (d a)) k) (by decide : (0 : Fin 2) ≠ 1) g h

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

abbrev whitKer (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Submodule ℂ X :=
  twKer (J.comp (secondEmb d)) (unipB k (Fin (d 1))) (whitChar ψ (d 1))

theorem whitKer_le_comap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) : whitKer ψ d J ≤ (whitKer ψ d J).comap (J (firstEmb d g)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, J (firstEmb d g) v, ?_⟩
  simp only [map_sub, map_smul, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, firstEmb_comm]

def whit2 (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Representation ℂ (GL (Fin (d 0)) k) (X ⧸ whitKer ψ d J) where
  toFun g := (whitKer ψ d J).mapQ (whitKer ψ d J) (J (firstEmb d g)) (whitKer_le_comap ψ d J g)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

theorem whit2_mk (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) (v : X) :
    whit2 ψ d J g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J (firstEmb d g) v) := rfl

theorem whitKer_le_comap_map (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    whitKer ψ d J ≤ (whitKer ψ d J').comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, f v, ?_⟩
  simp [f.isIntertwining]

def whitMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    (whit2 ψ d J).IntertwiningMap (whit2 ψ d J') :=
  .mk ((whitKer ψ d J).mapQ (whitKer ψ d J') f.toLinearMap (whitKer_le_comap_map ψ d f)) (fun g => by
    ext v
    simp [whit2_mk, f.isIntertwining])

end

end GlobalTheory.CompanionTheory.BZNuPair

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.Rodier

section Pi

variable {α : Type} [Fintype α] {Γ : α → Type} [∀ a, Group (Γ a)]

abbrev piSub (H : ∀ a, Subgroup (Γ a)) : Subgroup (∀ a, Γ a) := Subgroup.pi Set.univ H

def piChar {H : ∀ a, Subgroup (Γ a)} (χ : ∀ a, H a →* ℂˣ) : piSub H →* ℂˣ where
  toFun m := ∏ a, χ a ⟨m.1 a, m.2 a (Set.mem_univ a)⟩
  map_one' := Finset.prod_eq_one fun a _ => map_one (χ a)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => map_mul (χ a) ⟨x.1 a, x.2 a (Set.mem_univ a)⟩ ⟨y.1 a, y.2 a (Set.mem_univ a)⟩

end Pi

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

abbrev pm (w : Equiv.Perm (Fin N)) : GL (Fin N) k := GroundTheory.Automorphic.permGL k w

def cell (w : Equiv.Perm (Fin N)) : Set (GL (Fin N) k) :=
  {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k w * n}

def wKey (i : Fin N) : (Fin h)ᵒᵈ ×ₗ Fin N := toLex (OrderDual.toDual (blk (stdBlocks d hd) i), i)

def wOpen : Equiv.Perm (Fin N) := Tuple.sort (wKey d hd)

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def openFns (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) : Submodule ℂ (IndSp (stdBlocks d hd) ρ) where
  carrier := {f | ∀ g, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)}
  add_mem' := by
    intro a b ha hb g hg
    by_cases h1 : a.1.1 g = 0
    · refine hb g fun h2 => hg ?_
      show a.1.1 g + b.1.1 g = 0
      rw [h1, h2, add_zero]
    · exact ha g h1
  zero_mem' := fun g hg => absurd rfl hg
  smul_mem' := by
    intro c a ha g hg
    refine ha g fun h1 => hg ?_
    show c • a.1.1 g = 0
    rw [h1, smul_zero]

variable (k)

abbrev unipM : Subgroup (Levi k fun a => Fin (d a)) := piSub fun a => unipB k (Fin (d a))

variable {k}

abbrev whitM (ψ : AddChar k Circle) : unipM k d →* ℂˣ := piChar fun a => whitChar ψ (d a)

variable (k)

def unipU : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (unipRadLower k (stdBlocks d hd)).comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

def unipL : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (leviEmb k (stdBlocks d hd)).range.comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem OpenFactor.mem_unipL {u : GL (Fin N) k} : u ∈ unipL k d hd ↔
    u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ (leviEmb k (stdBlocks d hd)).range := by
  simp only [unipL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

end GlobalTheory.CompanionTheory.Rodier

namespace GlobalTheory.CompanionTheory.Rodier

def smInt {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : MeasureTheory.Measure X) (φ : X → W) : W :=
  ∑ᶠ v : W, (((μ (φ ⁻¹' {v})).toReal : ℝ) : ℂ) • v

end GlobalTheory.CompanionTheory.Rodier

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_principalSeriesSpace_of_indSp {n : ℕ} (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n))
      ((GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)) :
    (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) :=
  GlobalTheory.T.induced_in_principal_series k n α f

theorem isSatakeParameter_of_isSubquotient_of_injective {n : ℕ} (α : Fin n → ℂˣ) {X V : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) k) X}
    (hρ : IsSmooth ρ) (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))) (hι : Function.Injective ι)
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π ρ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  GlobalTheory.T.subquotient_principal_series_bound k n α X V ρ hρ ι hι π h μ

theorem KO_eq_integralGL (n : ℕ) : KO k (Fin n) = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := by
  ext v
  simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]

def bridge {n : ℕ} (α : Fin n → ℂˣ) :
    (prinSeries fun i => unrChar k (α i)).IntertwiningMap (principalSeries k n (paramChar k α)) where
  toFun f := ⟨fun g => f.1.1 g, mem_principalSeriesSpace_of_indSp α f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl)

theorem bridge_injective {n : ℕ} (α : Fin n → ℂˣ) : Function.Injective (bridge (k := k) α) := fun f f' e =>
  by
  have := congrArg Subtype.val e
  apply Subtype.ext
  apply Subtype.ext
  exact this

theorem isSatakeParameter_of_isSubquotient {n : ℕ} (α : Fin n → ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π (prinSeries fun i => unrChar k (α i)))
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  isSatakeParameter_of_isSubquotient_of_injective α (isSmooth_parInd _ _) (bridge α) (bridge_injective α) h μ

theorem hasSupport_prinSeries (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (π : IrrRep (GL (Fin n) k)) (h : IsSubquotient π.ρ (prinSeries χ)) :
    HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  have H : GlobalTheory.SmGL.IsCuspSupport π.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨π.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.CompanionTheory.SphSupp

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpherical_iff_fixedVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) :
    IsSpherical π ↔ GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.integralGL k n) ≠ ⊥ := by
  show fixed π (KO k (Fin n)) ≠ ⊥ ↔ _
  rw [KO_eq_integralGL, fixed_eq_fixedVectors]

end GlobalTheory.CompanionTheory.SphSupp
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem cas_mul_sub_mem_Jp (y : U n) (τ : Fin n → ℂ)
    (hd : ∀ k, e (k, k) * y - τ k • y ∈ Jp n)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * y ∈ Jp n) :
    Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y ∈ Jp n := by
  have key : ∀ a b : Fin n, e (a, b) * e (b, a) * y -
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y ∈ Jp n := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have hc : e (a, b) * e (b, a) - e (b, a) * e (a, b) = e (a, a) - e (b, b) := by
        simpa using e_mul_sub_mul (a, b) (b, a)
      have hcomm : e (a, b) * e (b, a) = e (b, a) * e (a, b) + (e (a, a) - e (b, b)) := by
        rw [← hc]; abel
      have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (b, a) * (e (a, b) * y) + (e (a, a) * y - τ a • y) - (e (b, b) * y - τ b • y) := by
        rw [if_neg h.ne, if_pos h, hcomm, zero_add, sub_smul]
        simp only [add_mul, sub_mul, mul_assoc]
        abel
      rw [hval]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (mul_mem_Jp _ (hu _ h)) (hd a)) (hd b)
    · subst h
      have hval : e (a, a) * e (a, a) * y -
          ((if a = a then τ a ^ 2 else 0) + (if a < a then τ a - τ a else 0)) • y =
          e (a, a) * (e (a, a) * y - τ a • y) + τ a • (e (a, a) * y - τ a • y) := by
        simp only [if_true, lt_irrefl, if_false, add_zero, mul_sub, mul_smul_comm, smul_sub,
          smul_smul, mul_assoc, pow_two]
        abel
      rw [hval]
      exact Submodule.add_mem _ (mul_mem_Jp _ (hd a)) (Submodule.smul_mem _ _ (hd a))
    · have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (a, b) * (e (b, a) * y) := by
        rw [if_neg h.ne', if_neg h.not_gt]
        simp [mul_assoc]
      rw [hval]
      exact mul_mem_Jp _ (hu _ h)
  have hsum : casC τ = ∑ a, ∑ b : Fin n,
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) := by
    simp only [casC, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hval : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y =
      ∑ a, ∑ b : Fin n, (e (a, b) * e (b, a) * y -
        ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y) := by
    rw [hsum]
    simp only [Formalism.REAL.Cas, Finset.sum_mul, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hval]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => key a b

theorem cas_mul_comm (x : U n) :
    x * Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) =
      Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x := by
  have hz : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) ∈ Subalgebra.center ℂ (U n) :=
    mem_center_of_commute_e fun a => by
      obtain ⟨c, d⟩ := a
      exact (Formalism.FourierDecayAlt.P.WigCas.cas_comm (glRel_e n) c d).symm
  exact (Subalgebra.mem_center_iff.1 hz) x

theorem upper_e_mem_Jp (a : Fin n × Fin n) (ha : IsUpper a) : e a ∈ Jp n :=
  vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))

theorem e_sub_rho_mem_Jp (u : U n) (k : Fin n) : u * e (k, k) - rhoVec n k • u ∈ Jp n := by
  have h := vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)
  have hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rwa [hv] at h

theorem casC_rho_add_eq (μ : Fin n → ℤ) (x : U n) (hw : IsAdW μ x)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hx : x ∉ Jp n) :
    casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  have h1 := cas_mul_sub_mem_Jp (1 : U n) (rhoVec n)
    (fun k => by simpa using e_sub_rho_mem_Jp (1 : U n) k) (fun a ha => by
      rw [mul_one]; exact upper_e_mem_Jp a ha)
  have h2 := cas_mul_sub_mem_Jp x (fun k => rhoVec n k + (μ k : ℂ)) (fun k => by
    have hv : e (k, k) * x - (rhoVec n k + (μ k : ℂ)) • x = x * e (k, k) - rhoVec n k • x := by
      have := hw k
      rw [add_smul, ← this]; abel
    rw [hv]; exact e_sub_rho_mem_Jp x k) hu
  have h3 := mul_mem_Jp x h1
  have hv : x * (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * 1 - casC (rhoVec n) • (1 : U n)) -
      (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x -
        casC (fun k => rhoVec n k + (μ k : ℂ)) • x) =
      (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n)) • x := by
    rw [mul_one, mul_sub, cas_mul_comm, mul_smul_comm, mul_one, sub_smul]; abel
  have h4 := Submodule.sub_mem _ h3 h2
  rw [hv] at h4
  by_contra hne
  apply hx
  have hc : casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n) ≠ 0 := sub_ne_zero.2 hne
  have := Submodule.smul_mem _ (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n))⁻¹ h4
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.CompanionTheory.PresRho
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.similitude_scaling_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | exact GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_identity_of_length_function : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) → (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) → ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish | exact GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem mapH_id_bij {K : Type} [Field K] (C : Cx.{1} K) (n : ℕ) :
    Function.Bijective ((Cx.Hom.id C).mapH n) := by
  have h : ∀ x : C.H n, (Cx.Hom.id C).mapH n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem swapPr_swapPr_apply {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K}
    (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ} (ha : a + a' = c)
    {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j) :
    (swapPr (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) ha).μ h x y = (pr ha).μ h x y := by
  simp only [swapPr, LinearMap.smul_apply, LinearMap.flip_apply, smul_smul]
  have s : ((-1 : ℤ) ^ (i * j) * (-1) ^ (j * i)) = 1 := by
    rw [mul_comm j i, ← mul_pow]
    simp
  rw [s, one_smul]

theorem glue_l : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hMV hCD K _ E U₂ ι _ _ V W hV hW h₁ h₂ hK
  let Rel : ObjectProperty E.C₁ → ObjectProperty E.D → Prop := fun U U' =>
    (∀ T, U' T → U (E.L₁.obj T)) ∧ (∀ T, U' T → U₂ (E.L₂.obj T))
  let prr : ∀ (U : ObjectProperty E.C₁) (U' : ObjectProperty E.D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c →
      CxPairing (CH.cx (U₂.ι ⋙ E.F₂ a)) (CH.cx (U.ι ⋙ E.F₁ a')) (CH.cx (U'.ι ⋙ E.F₃ c)) :=
    fun U U' r {a a' c} ha =>
      swapPr (P := fun a => CH.cx (U.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
        (T := fun c => CH.cx (U'.ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr U U₂ U' r.1 r.2 ha) ha
  have hnat : ∀ {U₁ U₂' : ObjectProperty E.C₁} {U₁' U₂'' : ObjectProperty E.D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂' U₂'')
      (k : U₂' ≤ U₁) (k' : U₂'' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n)
      (x : (CH.cx (U₂.ι ⋙ E.F₂ a)).X i) (y : CH.Cn (U₁.ι ⋙ E.F₁ a') j),
      (resU (E.F₃ c) k').pullC n ((prr U₁ U₁' r₁ ha).μ hn x y) = (prr U₂' U₂'' r₂ ha).μ hn x ((resU (E.F₁ a') k).pullC j y) := by
    intro U₁ U₂' U₁' U₂'' r₁ r₂ k k' a a' c ha i j n hn x y
    simp only [prr, swapPr, LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 k (le_refl U₂) k' (show a' + a = c by omega) (show j + i = n by omega) y x,
      GlobalTheory.T.restrict_self_pullC_eq (E.F₂ a) U₂ (le_refl U₂) i x]
  have key := GlobalTheory.T.cosieve_pairing_family_compat hMV hCD E.F₁ E.F₃ (fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) Rel prr hnat V W hV hW
    (fun S => ⟨h₁ S, h₂ S⟩) (fun S hS => GlobalTheory.T.kuenneth_swap _ (hK S hS))
  have k2 := GlobalTheory.T.kuenneth_swap _ key
  refine (GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _)
    (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) ?_).1 k2
  intro a a' c ha i j n h x y
  exact swapPr_swapPr_apply (P := fun a => CH.cx ((capU V ∅).ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
    (T := fun c => CH.cx ((capU W ∅).ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) ha) ha h x y

end GlobalTheory.CompanionTheory.KunGlue
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.filtered_cohomology_restriction_bijective : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ 0 X q κ))) (l s : ℕ)
    (hQ : (Q₀ = ⊤ ∧ l = 1) ∨ ∃ s', s ≤ s' ∧ Q₀ = TF l s') (𝒱 : Set X.Opens) (h : St (TF l s) 𝒱 ≤ St Q₀ 𝒱) (r r' : ℤ) (hr : r' ≤ s) (j : ℕ),
    Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.PDTrunc.pull_incl_bijective | exact GlobalTheory.CompanionTheory.PDTrunc.pull_incl_bijective | (intros; apply GlobalTheory.CompanionTheory.PDTrunc.pull_incl_bijective <;> assumption)
end
