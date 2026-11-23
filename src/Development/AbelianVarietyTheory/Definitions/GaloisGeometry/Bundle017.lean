module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KerJ.CharModel

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

section General

variable {L : Type} [Field L] [NumberField L]

theorem prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  apply _root_.GlobalTheory.Mem.Chr.Determ.exists_prod_inf_mul_finPart <;> assumption

theorem isFin_finPart (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

theorem isUnitary_of_orderDvd {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) : χ.IsUnitary := fun x => by
  have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
  have h2 : χ.1 x ^ n = 1 := by simpa using h1
  have h3 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

end General

variable {D : D7} {C : CharFrame D} (Dt : DtTied D C) {nch : NChoice D} (Tp : TupTied D C nch)

theorem eDt_finPart (a : Ideles D.host.E) : Dt.eDt (finPartI D.host.E a) = Dt.eDt a := by
  obtain ⟨y, hy⟩ := prod_inf_mul_finPart a
  conv_rhs => rw [← hy]
  rw [map_mul, map_prod, Finset.prod_eq_one fun w _ => Dt.inf w (y w), one_mul]


end GlobalTheory.KerJ.CharModel
end
end

section

noncomputable section

namespace GlobalTheory.TwV.Xc

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def phiA (A : LocAt F E n G) (v : Fin G.P.nV) : AfE F E →+* G.P.Qq v :=
  ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp ((A.ph v).comp (prV (E := E) (A.pl v).1))

def ordA (A : LocAt F E n G) (v : Fin G.P.nV) (x : (AfE F E)ˣ) : ℤ := ordP (G.P.W v) p (phiA A v (x : AfE F E))

def OneOff (w : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' (x : AfE F E) = 1

def SameOff (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} (x y : GL (Fin N) (AfE F E)) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → bc (prV (E := E) w') x = bc (prV (E := E) w') y

def PrimeOf (p : ℕ) (W : Type) {Q : Type} [CommRing W] [Field Q] [Algebra W Q] (ρ : E →+* Q) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Q y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)

def eMat {a N : ℕ} (hr : a = N) (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) : Matrix (Fin a) (Fin a) E :=
  (LinearMap.toMatrix' (stdG σ J γ).toLinearMap).submatrix (finCongr hr) (finCongr hr)

theorem phiA_incl (A : LocAt F E n G) (v : Fin G.P.nV) (x : E) : phiA A v (x ⊗ₜ[F] 1) = A.iw v x := by
  have hp : prV (E := E) (A.pl v).1 (x ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = x ⊗ₜ[F] 1 := by
    simp [prV]
  simp only [phiA, LocAt.iw, LocAt.phE, RingHom.comp_apply, hp]
  rfl

end GlobalTheory.TwV.Xc

end
end
