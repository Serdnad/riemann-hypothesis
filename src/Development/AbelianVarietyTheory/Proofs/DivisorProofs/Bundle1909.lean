module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.DblBoxTheta

open GlobalTheory.DblBox

theorem isThetaFunO_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  intro D ψ hψ S T f₁ f₂ h₁ h₂
  have ctop : Continuous (top : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  have cbot : Continuous (bot : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  let topH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' top top_add
  let botH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' bot bot_add
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    have e₁ : top (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e₂ : bot (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
    simp only [box, top_add, bot_add, symplOH_dbl]
    rw [e₁, e₂, h₁.quasi, h₂.quasi]
    rw [sub_eq_add_neg, neg_add, AddChar.map_add_eq_mul, neg_neg]
    simp only [psi_neg hψ, star_mul', star_star]
    ring
  · obtain ⟨U₁, hU₁o, hU₁⟩ := h₁.level
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂.level
    refine ⟨U₁.comap topH ⊓ U₂.comap botH, ?_, ?_⟩
    · exact (hU₁o.preimage ctop).inter (hU₂o.preimage cbot)
    · intro u hu hinf
      have hu₁ : top u ∈ U₁ := hu.1
      have hu₂ : bot u ∈ U₂ := hu.2
      have ht : (top u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inl i))) j
      have hb : (bot u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inr i))) j
      rw [heisO_box hψ, hU₁ _ hu₁ ht, hU₂ _ hu₂ hb]
  · exact (h₁.cont.comp ctop).mul ((h₂.cont.comp cbot).star)
  · intro k L hL hfin w
    have hf₁ :=
      h₁.smooth k (topH.comp L) (ctop.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inl i))) j) (top w)
    have hf₂ :=
      h₂.smooth k (botH.comp L) (cbot.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inr i))) j) (bot w)
    exact ContDiff.mul hf₁ (Complex.conjCLE.contDiff.comp hf₂)

end GlobalTheory.DblBoxTheta
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem hInv_quot_inf (q : ℕ) [NeZero q] (R : Type) [CommRing R] (I J : Ideal R)
    (hq : IsUnit (q : R)) (hI : HInv q (R ⧸ I)) (hJ : HInv q (R ⧸ J))
    (hIJ : HInv q (R ⧸ (I ⊔ J))) : HInv q (R ⧸ (I ⊓ J)) := by
  set K := I ⊓ J with hK
  let f := Ideal.Quotient.mk K
  have hqA : IsUnit (q : R ⧸ K) := by simpa using hq.map f
  have hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2
    have h1 : b - a ∈ K := Ideal.Quotient.eq.mp hab
    have haJ : a ∈ J := by
      have := J.sub_mem hb h1.2
      simpa using this
    have : f a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩
    rw [this]
    exact (nilradical (R ⧸ K)).zero_mem
  have eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
  have eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE inf_le_right
  have eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J) :=
    (Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ)
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eIJ.symm hIJ)

theorem ringKrullDim_quot_sup_succ_le (R : Type) [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : ¬ J ≤ p) : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hJ
  let g := Ideal.Quotient.mk p
  have hx0 : g x ≠ 0 := fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : g x ∈ nonZeroDivisors (R ⧸ p) := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE le_sup_left
  have h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) :=
    ringKrullDim_le_of_surjective e.toRingHom e.surjective
  have h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1 := by
    gcongr
    exact h3.trans h2
  exact h4.trans h1

theorem withBot_lt_of_add_one_le (a : WithBot ℕ∞) (d : ℕ) (h : a + 1 ≤ (d : WithBot ℕ∞)) :
    a < (d : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe] at h2
      simp at h2
    | coe n =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h
      have : n + 1 ≤ d := by exact_mod_cast h'
      have : n < d := by omega
      exact_mod_cast this

end GlobalTheory

namespace GlobalTheory

theorem hInv_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ),
    (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) →
    (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) →
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  intro q _ d hlt hdom R _ _ hq hd
  have key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance
    | insert p s hps ih =>
      intro hs
      have hp : p.IsPrime := hs p (Finset.mem_insert_self p s)
      have ihs := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      rw [Finset.inf_insert, id]
      by_cases hJ : s.inf id ≤ p
      · rw [inf_eq_right.mpr hJ]; exact ihs
      · haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ p))
          all_goals first | rfl | exact Subsingleton.elim _ _
        haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))
          all_goals first | rfl | exact Subsingleton.elim _ _
        refine hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_
        · exact hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p))
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
        · refine hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_
          refine withBot_lt_of_add_one_le _ d ?_
          exact (ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hN : hfin.toFinset.inf id = nilradical R := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]
    rfl
  have hred : HInv q (R ⧸ nilradical R) := by
    rw [← hN]
    refine key _ (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    exact hp.1.1
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.HeckeSplitGen.FinF

section Ports

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

theorem ev_sub (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a - b) Q = Φ a Q - Φ b Q := by
  rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp Φ) (y : E) (Q : HeightOneSpectrum (𝓞 E)) :
    Φ (incA F E y) Q = algebraMap E (Q.adicCompletion E) y := by rw [hΦ.2.2.1]; rfl

theorem isSplitIdem_of_delta (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {P : HeightOneSpectrum (𝓞 E)}
    (hc : cP hσ P ≠ P) {e : AE F E} (he : IsDelta Φ P e) : IsSplitIdem σ e := by
  obtain ⟨ε, hε⟩ := exists_placeIdem (F := F) (P.under (𝓞 F))
  obtain ⟨h0, h1, h2⟩ := place_comp (E := E) hΦ hε
  have he' := delta_conj hΦ hσ he
  refine ⟨delta_idem hΦ he, ?_, _, ε, hε, ?_⟩
  · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P
    · subst hQ
      rw [he'.2.2 Q (Ne.symm hc), mul_zero]
    · rw [he.2.2 Q hQ, zero_mul]
  · refine hΦ.ext' (by rw [RingHom.map_add (f := _), he.1, he'.1, add_zero, h0]) fun Q => ?_
    rw [ev_add]
    by_cases hQ : Q = P
    · subst hQ
      rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
    · by_cases hQ' : Q = cP hσ P
      · subst hQ'
        rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]
      · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']

theorem mem_modSet (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) (h0 : infPart F E (x : AE F E) = 1)
    (h : ∀ Q, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    x ∈ modSetF F E N := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨h0, ⟨finPart F E (((x : AE F E) - 1) * incA F E (N : E)⁻¹), (hΦ.2.2.2.1 _).2 fun Q => ?_, ?_⟩,
    (hΦ.2.2.2.1 _).2 fun Q => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_inv₀, map_natCast,
      Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (h Q).2 zero_le
  · have e : (N : AE F E) * incA F E (N : E)⁻¹ = 1 := by
      rw [← map_natCast (incA F E), ← map_mul, mul_inv_cancel₀ hN', map_one]
    have e2 : (x : AE F E) - 1 = N * (((x : AE F E) - 1) * incA F E (N : E)⁻¹) := by
      linear_combination (1 - (x : AE F E)) * e
    have e3 := congrArg (finPart F E) e2
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at e3
  · have e : Φ x Q * Φ (x⁻¹ : (AE F E)ˣ) Q = 1 := by rw [← ev_mul, Units.mul_inv, ev_one]
    have e2 := congrArg Valued.v e
    rw [Valuation.map_mul, (h Q).1, one_mul, Valuation.map_one] at e2
    exact e2.le

theorem mem_grpH_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) : (∀ P ∈ B, cP hσ P ≠ P) → ∀ x : (AE F E)ˣ,
      infPart F E (x : AE F E) = 1 →
      (∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) →
      x ∈ grpHF σ N := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    exact fun _ x h0 h => Subgroup.subset_closure (Or.inr (mem_modSet hΦ hN x h0 fun Q => h Q (Set.notMem_empty Q)))
  | @insert P B _ _ ih =>
    intro hB x h0 h
    obtain ⟨e, he⟩ := exists_delta hΦ P
    have hs := isSplitIdem_of_delta hσ hΦ (hB P (Set.mem_insert _ _)) he
    have h1 : GlobalTheory.HeckeSplitAll.Fin.part hs.1 x ∈ grpHF σ N := by
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨e, hs, ?_⟩))
      change (e + cA σ e) * (e * x + (1 - e) - 1) = e * x + (1 - e) - 1
      linear_combination ((x : AE F E) - 1) * hs.1 + ((x : AE F E) - 1) * hs.2.1
    have h2 : x * (GlobalTheory.HeckeSplitAll.Fin.part hs.1 x)⁻¹ ∈ grpHF σ N := by
      refine ih (fun Q hQ => hB Q (Set.mem_insert_of_mem _ hQ)) _ ?_ fun Q hQ => ?_
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub,
          RingHom.map_one, he.1, h0]
        simp
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, ev_add, ev_mul, ev_sub, ev_one]
        by_cases hQP : Q = P
        · subst hQP
          rw [he.2.1]
          simp
        · rw [he.2.2 Q hQP, zero_add, sub_zero, one_mul]
          exact h Q fun h' => h'.elim hQP hQ
    simpa using mul_mem h2 h1

theorem exists_fin_idem (hΦ : Comp Φ) :
    ∃ f : AE F E, f * f = f ∧ infPart F E f = 0 ∧ finPart F E f = 1 ∧ Φ f = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have he1 : ∀ z, (e z).1 = infPart F E z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart F E z := fun z => (he z).2
  obtain ⟨f, hf⟩ := e.surjective (0, 1)
  have hf0 : infPart F E f = 0 := by rw [← he1, hf]
  have hf1 : finPart F E f = 1 := by rw [← he2, hf]
  have key : ∀ g, infPart F E g = 0 → g * f = g := fun g hg => e.injective (Prod.ext
    (by rw [he1, he1, RingHom.map_mul, hg, zero_mul]) (by rw [he2, he2, RingHom.map_mul, hf1, mul_one]))
  refine ⟨f, key f hf0, hf0, hf1, ?_⟩
  obtain ⟨g, hg0, hg1⟩ := hΦ.2.1 1
  have h4 := congrArg Φ (key g hg0)
  rwa [map_mul, hg1, one_mul] at h4

theorem exists_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) (hB1 : ∀ P ∈ B, cP hσ P ≠ P) (x : (AE F E)ˣ)
    (h : ∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := exists_fin_idem hΦ
  have h3 : GlobalTheory.HeckeSplitAll.Fin.part hf x ∈ grpHF σ N := by
    refine mem_grpH_of_good hσ hΦ hN hB hB1 _ (GlobalTheory.HeckeSplitAll.Fin.map_mix_zero _ hf0 _) fun Q hQ => ?_
    have : Φ (GlobalTheory.HeckeSplitAll.Fin.part hf x : (AE F E)ˣ) = Φ x :=
      (GlobalTheory.HeckeSplitAll.Fin.map_mix_one Φ hf2 _).1
    rw [this]
    exact h Q hQ
  refine ⟨x * (GlobalTheory.HeckeSplitAll.Fin.part hf x)⁻¹, ?_, ?_⟩
  · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv]
    exact (GlobalTheory.HeckeSplitAll.Fin.map_mix_one _ hf1 _).2
  · rwa [mul_inv, inv_inv, mul_inv_cancel_left]

theorem exists_not_fixed (hσ : IsCMExt F E σ) : ∃ δ : 𝓞 E, cO σ δ ≠ δ := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (algebraMap F E) := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have ha : σ (a : E) = a := congrArg (fun t : 𝓞 E => (t : E)) (h a)
    have hb : σ (b : E) = b := congrArg (fun t : 𝓞 E => (t : E)) (h b)
    exact exists_of_conj_eq hσ (by rw [map_div₀, ha, hb])
  have h1 : Module.finrank F E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap F E).injective, hs⟩
  have h2 := hσ.2.2.1
  omega

theorem exists_finite_part_one_idele_split_congruence_quotient (hσ : IsCMExt F E σ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨Φ, hΦ⟩ := exists_comp F E
  obtain ⟨δ, hδ⟩ := exists_not_fixed hσ
  obtain ⟨m, hm, hm'⟩ := GlobalTheory.HeckeSplitAll.Fin.exists_den (Φ x)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hj : ∀ y : E, y ≠ 0 → ∃ u ∈ grpHF σ N, (u : AE F E) = incA F E y := fun y hy =>
    ⟨_, Subgroup.subset_closure (Or.inl (Or.inl ⟨Units.mk0 y hy, rfl⟩)), rfl⟩
  obtain ⟨a, ha, ha'⟩ := hj _ hm0
  have hx₁ : ∀ Q, Valued.v (Φ (a * x : (AE F E)ˣ) Q) ≤ 1 := fun Q => by
    rw [Units.val_mul, ha', ev_mul, ev_inc hΦ, map_natCast]
    exact hm' Q
  obtain ⟨y, hy, B, hB, hB1, hB2⟩ := GlobalTheory.HeckeSplitAll.Fin.approx_int
    ({ cO σ with invFun := cO σ, left_inv := fun t => cO_cO hσ t, right_inv := fun t => cO_cO hσ t } : 𝓞 E ≃+* 𝓞 E)
    (fun t => cO_cO hσ t) δ hδ N hN (Φ (a * x : (AE F E)ˣ))
    (Φ ((a * x)⁻¹ : (AE F E)ˣ)) (by rw [← map_mul, Units.mul_inv, map_one]) hx₁
  obtain ⟨b, hb, hb'⟩ := hj _ (inv_ne_zero hy)
  obtain ⟨z, hz, hz'⟩ := exists_of_good hσ hΦ hN hB
    (fun P hP h => hB1 P hP fun t ht => (mem_cP hσ P t).1 (h.symm ▸ ht)) (a * x * b) fun Q hQ => by
      rw [Units.val_mul, hb', ev_mul, ev_inc hΦ, map_inv₀]
      exact hB2 Q hQ
  exact ⟨z, hz, GlobalTheory.HeckeSplitAll.Fin.mem_of_mul_mem ha hb hz'⟩

end Ports

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem exists_finPart_eq_one_mul_inv_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  intro F E _ _ _ _ _ σ hσ N hN x
  exact exists_finite_part_one_idele_split_congruence_quotient hσ hN x

end GlobalTheory.HeckeSplitGen.FinF

end
end

section

theorem GlobalTheory.CubeTop.cubeTheorem : GlobalTheory.Published.CubeTheorem := GlobalTheory.SpreadingModels.cubeTheorem_holds
end
