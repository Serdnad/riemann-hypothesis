module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle592
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct




namespace GlobalTheory.SeriesTie

theorem linearIndependent_rows_map {K L : Type*} [Field K] [Field L] (e : K →+* L) {n m : ℕ}
    (a : Fin n → Fin m → K) (ha : LinearIndependent K a) :
    LinearIndependent L fun c k => e (a c k) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha.fintypeLinearCombination_injective)
  have hj : ∀ c j, g (a c) j = if c = j then 1 else 0 := fun c j => by
    have := congrFun (LinearMap.congr_fun hg (Pi.single c 1)) j
    simpa [Pi.single_apply, eq_comm] using this
  have hg' : ∀ (x : Fin m → K) j, g x j = ∑ k, x k * g (fun j' => if k = j' then 1 else 0) j := fun x j => by
    conv_lhs => rw [pi_eq_sum_univ x]

    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  intro μ hμ j
  have h0 : ∀ k, ∑ c, μ c * e (a c k) = 0 := fun k => by
    have := congrFun hμ k
    simpa [Finset.sum_apply] using this
  calc μ j = ∑ c, μ c * e (g (a c) j) := by simp [hj]
    _ = ∑ c, ∑ k, μ c * e (a c k * g (fun j' => if k = j' then 1 else 0) j) :=
        Finset.sum_congr rfl fun c _ => by rw [hg' (a c) j, map_sum, Finset.mul_sum]
    _ = ∑ k, e (g (fun j' => if k = j' then 1 else 0) j) * ∑ c, μ c * e (a c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by simp [h0]

theorem realRd_faithful : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), ν ≠ 0 → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → (S.A ((j : ℕ) + 1)).IsKsForm → Faithful (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hν hU hW hv hK
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.Fm S i ((j : ℕ) + 1) b) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  intro n v hvi
  let w : Fin n → NX.Fm S i ((j : ℕ) + 1) b := fun c => YS.eF i _ b (Nat.le_add_left _ _) j.2 (v c)
  have hw0 : LinearIndependent (FractionRing (D.ntw.O i)) w :=
    hvi.map' (YS.eF i _ b (Nat.le_add_left _ _) j.2).toLinearMap (YS.eF i _ b (Nat.le_add_left _ _) j.2).ker
  have hw1 : LinearIndependent (NX.KB S i b) w := hw0
  have hw : LinearIndependent (NX.KB S i b) fun c => B.equivFun (w c) :=
    hw1.map' B.equivFun.toLinearMap B.equivFun.ker
  have hr := linearIndependent_rows_map (ρ.e i b) (fun c => B.equivFun (w c)) hw
  let Ψ : (Fin m → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) := ν⁻¹ • Fintype.linearCombination ℂ φ
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have h0 : Fintype.linearCombination ℂ φ z = 0 := by
      have := hz
      simp only [Ψ, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hν, false_or] at this
      exact this
    exact hφ.fintypeLinearCombination_injective (h0.trans (map_zero _).symm)
  suffices key : (fun c => realRd YS v₀ hρ i j b ν (v c)) = Ψ ∘ fun c k => ρ.e i b (B.equivFun (w c) k) by
    rw [key]; exact hr.map' Ψ hΨ
  funext c
  change ν⁻¹ • evK YS v₀ hρ i j b (w c) = ν⁻¹ • Fintype.linearCombination ℂ φ _
  congr 1
  rw [Fintype.linearCombination_apply]
  conv_lhs => rw [← B.sum_equivFun (w c)]
  refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bK k : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) from
    Algebra.TensorProduct.basis_apply _ _]
  change evK YS v₀ hρ i j b ((B.equivFun (w c) k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) = _
  rw [smul_eq_mul, mul_one]
  refine (evK_tmul YS v₀ hρ i j b _ _).trans ?_
  exact congrArg _ (congrArg (evW YS v₀ j) (hbK k))

end GlobalTheory.SeriesTie
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem conjPl_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem splitSet_of_split {S : Finset (Pl D.host.E)} (hs : ∀ P ∈ S, IsSplitPl D.host P)
    (hn : ∀ P ∈ S, ∀ P' ∈ S, ¬ IsConjPl D.host P P') : SplitSet S := by
  refine GlobalTheory.GridIdem.exists_isIdemSum S (fun P hP => GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne_of_split (hs P hP)))
    fun P hP P' hP' h => ?_
  rcases (GlobalTheory.Mem.TypePl.under_eq_iff P P').1 h.symm with e | e
  · exact e.symm
  · exact absurd e (hn P hP P' hP')

end GlobalTheory.UnivGood

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem univOf_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ),
      (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).Good (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) := by
  intro D N X ρ hρ Y i Q M
  classical
  set A := admissibleConjugatePairPlaces X i Q M with hA
  have hAconj : ∀ P ∈ A, ∀ P', IsConjPl D.host P P' → P' ∈ A := fun P hP P' hc => conj_mem_admissibleConjugatePairPlaces hP hc
  have hsplit : SplitSet (half (ρ.ch i) A) := by
    refine splitSet_of_split (fun P hP => isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) hc
    exact ((hρ.ch i).pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  refine ⟨hsplit, fun PP hPP => ?_⟩
  have hPA : PP ∈ A := (mem_half.1 hPP).1
  obtain ⟨-, P', hP'Q, hc, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPA
  have hP'A : P' ∈ A := conj_mem_admissibleConjugatePairPlaces hPA hc
  set φ := coord Y i A M PP with hφ
  have hco : ∀ σ, Multiplicative.toAdd (φ σ) = Multiplicative.toAdd (Y.delU i A M σ) ⟨PP, hPA⟩ :=
    fun σ => coord_apply Y i A M hPA σ
  have hord : ∀ σ, ∃ n : ℕ, φ σ ^ (X.l i ^ n) = 1 := fun σ => ⟨M, by
    rw [← ofAdd_toAdd (φ σ), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩
  have hopen : IsOpen (φ.ker : Set (G D.host.E N.Om)) := by
    refine Subgroup.isOpen_mono (H₁ := (Y.delU i A M).ker) (fun g hg => ?_) (Y.delU_open i A M)
    refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
    rw [hco, MonoidHom.mem_ker.1 hg]
    rfl
  have hanti : AntiHom X.cc φ := fun g g' hg => by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_inv, hco, hco, Y.delU_anti i A M g g' hg, toAdd_inv]
    rfl

  have hpair : ∀ x ∈ ({PP, P'} : Finset (Pl D.host.E)), ∀ y, IsConjPl D.host x y → y ∈ ({PP, P'} : Finset (Pl D.host.E)) := by
    intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [GlobalTheory.GalChar.isConjPl_unique hy hc]; simp
    · rw [Finset.mem_singleton] at hx
      subst hx
      rw [GlobalTheory.GalChar.isConjPl_unique hy (GlobalTheory.GalChar.isConjPl_symm hc)]; simp
  have hsub : ({PP, P'} : Finset (Pl D.host.E)) ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hPA
    · rw [Finset.mem_singleton] at hx; subst hx; exact hP'A
  have hunr : ∀ v : Pl D.host.E, v ∉ ({PP} : Finset (Pl D.host.E)) →
      (∀ P ∈ ({PP} : Finset (Pl D.host.E)), ¬ IsConjPl D.host P v) →
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1 := by
    intro v hv hnc B hB σ hσ
    have hv' : v ∉ ({PP, P'} : Finset (Pl D.host.E)) := by
      intro h
      rcases Finset.mem_insert.1 h with rfl | h
      · exact hv (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton] at h
        subst h
        exact hnc PP (Finset.mem_singleton_self _) hc
    refine Multiplicative.toAdd.injective ?_
    rw [hco, ← Y.delU_res i M {PP, P'} A hsub hpair hAconj σ PP (by simp),
      Y.delU_unr i {PP, P'} M v hv' B hB σ hσ]
    rfl
  have hl : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact (hadm.1 P (by simp)).2
  have hg := GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc (Multiplicative (ZMod (X.l i ^ M))) φ (X.l i) (X.lPrime i).out hord hopen
    hanti {PP} (hsplit.mono (Finset.singleton_subset_iff.2 hPP)) hl hunr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  refine ⟨h1, h2, h3, h4, h5, fun P hP => ?_⟩
  rw [Finset.mem_singleton] at hP
  subst hP
  exact h6 _ (Finset.mem_singleton_self _)

end GlobalTheory.UnivGood
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HeckeDetChar

open Formalism.L2.JoinChr
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem place_eq {e : AE D} {P P' : Pl D.host.E} (h : IsIdemAt e P) (h' : IsIdemAt e P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [h.2 x hx, h'.2 x hx]

theorem finPart_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem finPart_mul_incA_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) {x : D.host.E}
    (hx : P.valuation D.host.E x ≤ 1) : finPart D (e * incA D x) ∈ intAE D := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0; apply hd0; exact RingOfIntegers.ext h0
  have hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdE]; exact h
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D :=
    not_not.1 (mt (he.2 _ hd0).2 hd)
  rw [hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) =
    incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]
  exact GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1

theorem idem_mul_eq_zero {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) {P : Pl D.host.E}
    (hoff : Bridge.SplitOff P (Q : Set (Pl D.host.E))) {e : AE D} (he : IsIdemAt e P) :
    (idem Q + cA D (idem Q)) * e = 0 := by
  have hc : IsIdemAt (cA D e) (conjPl P) := GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl

  rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun Q' hQ' => ?_
  have he' := hS.isIdemAt hQ'
  rw [add_mul]
  have a1 : idemAt Q' * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h
    · rw [h] at he'
      exact absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1
    · exact h
  have a2 : cA D (idemAt Q') * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h
    · rw [h] at he'
      have hPQ := place_eq hc he'
      refine absurd ?_ (hoff.2.2 Q' hQ')
      rw [← hPQ]
      ext x
      rw [Formalism.L2.Col.mem_conjIdeal]
      rfl
    · have := congrArg (cA D) h
      rwa [map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero] at this
  rw [a1, a2, add_zero]

theorem chi_eq_one {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hχ : GlobalTheory.ExportSeries.UnramOutside χ Q)
    {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) (hQ : (idem Q + cA D (idem Q)) * e = 0) (x : (AE D)ˣ)
    (y y' : AE D) (hx : (x : AE D) = 1 + e * (y - 1)) (hx' : ((x⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (y' - 1))
    (hy : finPart D (e * y) ∈ intAE D) (hy' : finPart D (e * y') ∈ intAE D) : χ x = 1 := by
  have key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D := fun w hw => by
    rw [show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one]
    exact add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw
  refine hχ x ?_ ?_ ?_ ?_
  · rw [hx, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]
  · rw [hx]; exact key y hy
  · rw [hx']; exact key y' hy'
  · rw [hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]

theorem locE_pow {e : AE D} (he : e * e = e) (a : AE D) (k : ℕ) :
    (1 + e * (a - 1)) ^ k = 1 + e * (a ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    linear_combination (a ^ k - 1) * (a - 1) * he

theorem isPlIdem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : IsPlIdem D e P := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := he
  exact ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩

theorem locU_inv {e : AE D} (he : e * e = e) (k : D.host.Eˣ) :
    (((locU he k)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
  have hmul : locU he k * locU he k⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]
    simp [locE]
  rw [inv_eq_of_mul_eq_one_right hmul, locU_val]

theorem val_unif {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hP2 (zero_mem _)
  rw [show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]
  have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
  have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
  rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
  rw [WithZero.exp_le_exp] at a2
  congr 1
  push_cast at a2
  omega

theorem chi_detAt : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {c : Formalism.L2.Host.HChar D.host.E}, ChrEq χ c →
    ∀ {Q : Finset (Pl D.host.E)}, GlobalTheory.ExportSeries.UnramOutside χ Q → GlobalTheory.ExportSeries.SplitSet Q → ∀ {P : Pl D.host.E},
    Bridge.SplitOff P (Q : Set (Pl D.host.E)) → ∀ {V : HSp D} {k : ℕ} {α : GA D V}, IsHeckeAt V P k α →
    ∀ {z : (AE D)ˣ}, IsDetAt (idemAt P) V α z → ((χ z : Circle) : ℂ) = ((c.val P : ℂˣ) : ℂ) ^ k := by
  intro D χ c hχc Q hU hS P hoff V k α hα z hz
  obtain ⟨e, ϖ, he, hϖP, hϖP2, hH⟩ := hα
  rw [idemAt_eq he] at hz
  obtain ⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩ := hH
  have hQe := idem_mul_eq_zero hS hoff he
  have hee : e * e = e := he.1.1
  have hv := val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU

  let wU : (AE D)ˣ := ⟨1 + e * (u - 1), 1 + e * (u' - 1),
    by linear_combination (u - 1) * (u' - 1) * hee + huu,
    by linear_combination (u - 1) * (u' - 1) * hee + huu⟩
  have hw : χ wU = 1 := chi_eq_one hU he hQe wU u u' rfl rfl
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu)
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')

  have hz' : z = locU hee ϖU ^ k * wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]
    show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))
    linear_combination hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee

  have h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)

  set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU
  have hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) := by
    have := Formalism.L2.Host.unif_spec P
    unfold Formalism.L2.Host.IsUnifAt at this
    rw [← this]
    show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  have hvr : P.valuation D.host.E (rU : D.host.E) = 1 := by
    rw [hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hr1 : χ (locU hee rU) = 1 := by
    refine chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl
      (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]
  have hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)
  rw [hr1] at hr2
  have hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ) := by
    have : ϖU = rU * Formalism.L2.Host.unif P := by rw [hrU, inv_mul_cancel_right]
    rw [this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]
    simp
  rw [hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]

end GlobalTheory.HeckeDetChar
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.adelicGLLastRow_and_detModule_under_left_multiplication : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  first | (exact @GlobalTheory.UnfoldRows.rows_main) | (exact GlobalTheory.UnfoldRows.rows_main) | (intros; apply GlobalTheory.UnfoldRows.rows_main  <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

theorem _root_.GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  first | exact @GlobalTheory.ZUnf.good_fT | exact GlobalTheory.ZUnf.good_fT | (intros; apply GlobalTheory.ZUnf.good_fT <;> assumption)
end
