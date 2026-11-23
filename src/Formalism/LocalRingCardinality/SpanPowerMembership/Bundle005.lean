module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle003
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows

@[expose] public section

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem continuous_rHom : Continuous (rHom (E := E) hj) :=
  by apply _root_.UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom <;> assumption

instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact

def eDec : ↥(Dec (F := E) A) ≃* ↥(KwF (E := E) j).fixingSubgroup :=
  (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).symm

theorem eDec_comm (g : ↥(Dec (F := E) A)) (x : Ω) :
    ((eDec hj g : ↥(KwF (E := E) j).fixingSubgroup) : GQ l) (j x) = j ((g : G E Ω) x) := by
  rw [← j_rHom hj]
  congr 2
  exact congrArg Subtype.val ((MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).apply_symm_apply g)

theorem continuous_eDec_symm : Continuous (eDec (E := E) hj).symm := continuous_rHom hj

theorem continuous_eDec : Continuous (eDec (E := E) hj) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).toEquiv)
    (continuous_rHom hj)

end Formalism.BasicNotions.Examples₂.LB

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

end Formalism.BasicNotions.Examples₂
end
end

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LevelValuationRings

open Formalism.MainNotions.G QuadraticAlgebra

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

abbrev Wn : Type := WittVector p (GaloisField p n)

abbrev Qn : Type := FractionRing (Wn p n)

abbrev On : Type := QuadraticAlgebra (Wn p n) (p : Wn p n) 0

instance instDomOn : IsDomain (On p n) := GatR.isDomain (WittVector.irreducible p)
instance instDvrOn : IsDiscreteValuationRing (On p n) := GatR.isDVR (WittVector.irreducible p)

abbrev Kn : Type := FractionRing (On p n)

def sigN : Qn p n ≃+* Qn p n :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (GaloisField p n))

theorem sigN_alg (x : Wn p n) :
    sigN p n (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) (WittVector.frobenius x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

theorem inj_WK : Function.Injective ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) :=
  (IsFractionRing.injective (On p n) (Kn p n)).comp algebraMap_injective

def iotaN : Qn p n →+* Kn p n := IsFractionRing.lift (inj_WK p n)

theorem frob_iter (hn : n ≠ 0) (x : Wn p n) : (WittVector.frobenius^[n]) x = x := by
  ext i
  rw [WittVector.iterate_frobenius_coeff]
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h := FiniteField.pow_card (x.coeff i)
  rwa [← Nat.card_eq_fintype_card, GaloisField.card p n hn] at h

theorem sigN_pow_alg (k : ℕ) (x : Wn p n) :
    (sigN p n ^ k) (algebraMap (Wn p n) (Qn p n) x) =
      algebraMap (Wn p n) (Qn p n) ((WittVector.frobenius^[k]) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    show sigN p n ((sigN p n ^ k) _) = _
    rw [ih, sigN_alg]

theorem sigN_period (hn : n ≠ 0) : sigN p n ^ n = 1 := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Wn p n))
  ext1 x
  show (sigN p n ^ n) (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) x
  rw [sigN_pow_alg, frob_iter p n hn]

theorem hidaSettingOfEven (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (Wn p n) (Qn p n) (On p n) (Kn p n) (iotaN p n) (sigN p n)
      (algebraMap (Wn p n) (On p n)) ω := by
  exact {
    prime := hp.out
    five_le := h5
    two_le := h2
    even := he
    frac_alt := inferInstance
    frac_O := inferInstance
    p_unif := WittVector.irreducible p
    res_card := by
      rw [Nat.card_congr (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)).toEquiv,
        GaloisField.card p n (by omega)]
    eq_sum_herm_smul_frame_of_inW := inferInstance
    frob := fun x => by
      have h : WittVector.frobenius x - x ^ p ∈ Ideal.span {(p : Wn p n)} := by
        rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
        show WittVector.constantCoeff (WittVector.frobenius x - x ^ p) = 0
        rw [map_sub, map_pow]
        show (WittVector.frobenius x).coeff 0 - x.coeff 0 ^ p = 0
        rw [WittVector.coeff_frobenius_charP, sub_self]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp h
      exact ⟨y, by rw [sigN_alg, ← hy]; congr 1; ring⟩
    period := sigN_period p n (by omega)
    ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
    finite := RingHom.finite_algebraMap.mpr inferInstance
    complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
    w_sq := by rw [GatR.om_sq, map_natCast]
  }

end Formalism.BasicNotions.Examples₂.LevelValuationRings
end
end

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)

end Gen

end Formalism.BasicNotions.Examples₂.NZ
end
end

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime]

section Emb

variable {F : Type} [Field F] [NumberField F]

def Kphi (φ : F →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => φ (Module.finBasis ℚ F i))

instance Kphi_fin (φ : F →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (Kphi φ) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem phi_mem (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by
  have hx := (Module.finBasis ℚ F).sum_repr x

  rw [← hx, map_sum]
  refine sum_mem (fun i _ => ?_)
  rw [map_rat_smul, Rat.smul_def]
  refine mul_mem ?_ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  first
  | exact SubfieldClass.ratCast_mem _ _
  | exact ratCast_mem _ _
  | exact (Kphi φ).toSubfield.ratCast_mem _
  | simp


theorem exists_embAt (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
  have hAl : (placeOf (AlgebraicClosure F) w).valuation ((l : ℕ) : AlgebraicClosure F) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 F)).mpr hw
    simpa using this
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) := isAlgClosureQ F (AlgebraicClosure F)
  obtain ⟨j, hj⟩ := exists_emb (l := l) _ hAl
  exact ⟨j.comp (algebraMap F (AlgebraicClosure F)), fun x => by
    rw [← hA x, val_lt_one_iff hj]; rfl⟩

end Emb


section Mu

variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)


end Mu

end Formalism.BasicNotions.Examples₂.LB
end
end
