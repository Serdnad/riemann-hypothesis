module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLatInst
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


open Classical in
def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

variable {Ch sel mu cst Λ}

end One

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end Chain

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem first_sum_scalar_mul {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (psi : k → K) (vals : Finset k) (wt : K) (a : K)
    (Φ : Loc.SF k K (n' + c') (n + c)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => a * Φ x) xj = a * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj := by
  unfold Loc.E1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end Pts

section Res

variable {k : Type} [CommRing k]

end Res

section Assemble

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

end Assemble

section Deep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

end Deep

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def ChIdx.withTop (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q) : ChIdx X Pr R Q where
  β j := {b : Option (L.β j) // b.isSome = decide (j ≤ m2 + 1)}
  h j b P := match b.1 with
    | some b' => L.h j b' P
    | none => 1
  levG j b := match b.1 with
    | some b' => L.levG j b'
    | none => Λt j
  levQ j b := match b.1 with
    | some b' => L.levQ j b'
    | none => Θt j

variable (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q)

def ChIdx.top {j : ℕ} (hj : m2 + 1 < j) : (L.withTop m2 Λt Θt).β j := ⟨none, by simp [Nat.not_le.2 hj]⟩

end Top

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QFr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (Pl E)}

theorem qdf_frame_ratio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n)
    (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    ∀ y, (p'.fr P).symm (γ (p.fr P y)) ∈ stdAt E n P.1 ↔ y ∈ stdAt E n P.1 := by
  intro y
  have h1 := p'.2 P ((p'.fr P).symm (γ (p.fr P y)))
  have e1 : p'.1.2 P ((p'.fr P).symm (γ (p.fr P y))) = γ (p.fr P y) := LinearEquiv.apply_symm_apply _ _
  rw [e1] at h1
  rw [← h1]
  show γ (p.fr P y) ∈ localization₂ P.1.asIdeal p'.1.1.1.N ↔ _
  have hN' : p'.1.1.1.N = gmap γ p.1.1.1.N := hN
  rw [hN', mem_localization_gmap, LinearEquiv.symm_apply_apply]
  exact p.2 P y

def qdRatio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    GLint E n P.1 :=
  ⟨(p.fr P).trans (γ.trans (p'.fr P).symm), fun y => qdf_frame_ratio p p' γ hN P y⟩

end QFr

section QEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {K : Type} [Field K]

end QEmpty

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section NbFunI

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

def nbFunI (P : Ideal (𝓞 E)) (s : List ℕ) : (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) →ₗ[K] (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) where
  toFun ψ d := ∑ d₁ ∈ d.inertNb P s, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFunI

section Tr

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem trF_nbFunI {V : Type} [AddCommGroup V] [Module X.K V] (a : GLG (E := X.E) (n := n) (SG := SG)) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (ψ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → V) :
    trF X n ST SG V a (nbFunI X.K V P s ψ) = nbFunI X.K V P s (trF X n ST SG V a ψ) := by
  funext d
  show ∑ d₁ ∈ (((1 : UF X.E n), a⁻¹) • d).inertNb P s, ψ d₁ =
    ∑ d₁ ∈ d.inertNb P s, ψ (((1 : UF X.E n), a⁻¹) • d₁)
  exact DecoSet.sum_inertNb_smul P s _ d ψ

variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem heckeFamI_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ)
    (φ : (formGSD C Λ).EqFun) :
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
      nbFunI X.K C.V y.1.1.asIdeal y.2 (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) := by
  funext d
  show ((heckeI (Formalism.L2.DIV.formPts C Λ) y.1.1.asIdeal y.2).op φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d =
    ∑ d₁ ∈ DecoSet.inertNb y.1.1.asIdeal y.2 d, (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d₁
  rw [heckeI_op_apply]
  simp [DecoPts.nbI, Formalism.L2.DIV.formPts]

theorem heckeFamI_comm_trRep {A : Type} [Group A] (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ) (a : A) :
    Commute (trRep C Λ ι hι a) (heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y) := by
  show trRep C Λ ι hι a * heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y =
    heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y * trRep C Λ ι hι a
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Module.End.mul_apply, Module.End.mul_apply]
  show trF X n ST SG C.V (ι a)
      ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y (trRep C Λ ι hι a φ) : (formGSD C Λ).EqFun) :
      DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V)
  rw [heckeFamI_formPts_apply, heckeFamI_formPts_apply, trF_nbFunI]
  rfl

end Tr

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem weylDim_of_weylProd (h : PI.WeylProd) {n : ℕ} (lam : DomWeight n) : WeylDim lam := by
  unfold WeylDim
  rw [Formalism.L2.G.Model.card_ssIdx]
  have hnn : ∀ t, ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.detShift := by
    intro t
    unfold DomWeight.natW
    apply Int.toNat_of_nonneg
    unfold DomWeight.detShift
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) t.isLt
    rw [dite_eq_left hn]
    have h1 : t ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      rw [Fin.le_def]
      have := t.isLt
      show t.val ≤ n - 1
      omega
    have := lam.anti h1
    omega
  have hanti : Antitone (fun t => ((lam.natW t : ℕ) : ℤ)) := by
    intro a b hab
    have := lam.anti hab
    simp only [hnn]
    omega
  have h1 := Formalism.L2.G.Model.weylQ n _ hanti
  have h2 : _ = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n := h n (fun t => ((lam.natW t : ℕ) : ℤ)) lam.w lam.detShift hnn
  rw [← h2, ← h1, Rat.cast_natCast]

theorem weylDim_holds {n : ℕ} (lam : DomWeight n) : WeylDim lam := weylDim_of_weylProd weyl_product_formula lam

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Inst

end Formalism.L2.Col
end
end
