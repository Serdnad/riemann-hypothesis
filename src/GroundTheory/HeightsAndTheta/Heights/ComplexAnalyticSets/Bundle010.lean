module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ringKrullDim_quotient_eq_coheight {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]

theorem height_add_ringKrullDim_quotient_le {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩

theorem height_map_add_one_le_of_mem_nonZeroDivisors {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by
  set I := Ideal.span {y} with hI
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm
  rw [hn]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I))
    (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)
  let f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hab ⊢
      exact Ideal.comap_mono hab
    · ext1
      have := congrArg PrimeSpectrum.asIdeal hab
      exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
  let L := l.map f hf
  have hyhead : y ∈ L.head.asIdeal := by
    change y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le
  let p0 : PrimeSpectrum B := ⟨p, hp.1.1⟩
  have hlt : p0 < L.head := by
    refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_
    have hyp : y ∈ p := by
      have : p = L.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [this]
      exact hyhead
    exact Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩
  let L' := L.cons p0 hlt
  have hLlast : L'.last = ⟨P, hP⟩ := by
    simp only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]
    ext1
    exact Ideal.comap_map_mk hIP
  have hlen' : L'.length = n + 1 := by
    simp [L', L, hlen]
  have := Order.length_le_height_last (p := L')
  rw [hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight] at this
  exact_mod_cast this

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def IdealHeightSpread.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime], I ≤ P →
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], I ≤ Q → g ∉ Q →
      (I.map (algebraMap R (Localization.AtPrime P))).height ≤
        (I.map (algebraMap R (Localization.AtPrime Q))).height

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

universe u

def RegularSequenceLengthLeDim.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → (rs.length : WithBot ℕ∞) ≤ ringKrullDim R

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ExtensionQuotientLength.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (r : R),
    Function.Injective (algebraMap R B) → algebraMap R B r ∈ nonZeroDivisors B →
    Module.length R (B ⧸ LinearMap.range (Algebra.linearMap R B)) ≠ ⊤ →
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R (B ⧸ Ideal.span {algebraMap R B r})

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem isPrime_map_quotient_localization {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)

def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutGlobal.Statement : Prop :=
  ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
    IsNilpotent P → IsPrincipalIdealRing (C ⧸ P) → y ∉ P → (P ⊔ Ideal.span {y}).IsMaximal →
      (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (M ⧸ (Ideal.span {y} • ⊤ : Submodule C M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutLocalizedModule.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B) (Q₀ : Ideal B) [Q₀.IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M],
    IsNilpotent P → y ∉ P → Q₀ = P ⊔ Ideal.span {y} → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length (Localization.AtPrime Q₀)
          (LocalizedModule Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M))) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthLocalizedLocalized.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M],
    P ≤ Q →
      Module.length (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (LocalizedModule (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
            (LocalizedModule Q.primeCompl M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

theorem LengthLocalizedLocalized.map_isPrime (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP
    (Set.disjoint_left.mpr fun _ hx hxP => hx (h hxP))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def LengthLocalizedQuotient.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B),
    minimalPrimes B = {P} → (∀ s ∉ P, s ∈ nonZeroDivisors B) → y ∉ P →
    ∀ (Q : Ideal (B ⧸ Ideal.span {y})) [Q.IsPrime], Q.comap (Ideal.Quotient.mk _) = P ⊔ Ideal.span {y} →
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

def LocalizationAtPrimeQuotient.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) (T : Submonoid (A ⧸ I)) (P : Ideal (Localization T)) [P.IsPrime]
    (W : Ideal A) [W.IsPrime],
    P.comap ((algebraMap (A ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) = W →
      ∃ e : Localization.AtPrime P ≃+* (Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))),
        ∀ a : A,
          e (algebraMap (Localization T) (Localization.AtPrime P)
              (algebraMap (A ⧸ I) (Localization T) (Ideal.Quotient.mk I a))) =
            Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime W)))
              (algebraMap A (Localization.AtPrime W) a)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def CotangentBasisInPrime.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime],
    ∃ (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) ∧
      maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def FlatLocalRegularSequence.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ∀ (rs : List A) (ys : List B), (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular A rs →
        (∀ y ∈ ys, y ∈ maximalIdeal B) →
        IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (ys.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) →
        IsWeaklyRegular B (rs.map (algebraMap A B) ++ ys)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
