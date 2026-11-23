module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj.SqNum

theorem not_unrAt_alpha_div_beta_over_S₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hw
  have e : alpha G t i j / beta G i j = G.nu t i ((j : ℕ) + 1) := by
    simp only [alpha, beta, GridData.nu]
    exact mul_div_mul_right_eq_div _ _ _
  rw [e, GlobalTheory.LFun.unrAt_iff_of_chrEq (chrEq_nu (G := G) (t := t) (i := i) (j := j) hL) w]
  intro hu
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine (G.ch.lev1 _ hi1 hi2 w hw).2 fun x hx h1 => ?_
  have a1 := (L.C.isMu0 j).tame w x hx h1
  have a2 := hL.xi_tame t w x hx h1
  have a3 := hu x hx
  change ((L.C.mu0 j).loc w x * (L.xiH t).loc w x) *
    ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ = 1 at a3
  rw [a1, a2, one_mul, one_mul] at a3
  exact inv_eq_one.1 a3

end GlobalTheory.FunObj.SqNum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaGridRamifiedOverBasePlace

theorem thetaGridCharacterQuotient_not_unramified_over_basePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hv
  rw [show alpha G t i j / beta G i j = G.nu t i (j + 1) from mul_div_mul_right_eq_div _ _ _,
    GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) w]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : ¬ (G.ch.chiH (D.R.m - i)).UnrAt w := (G.ch.lev0 _ hm.1 hm.2 _ hv).2
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    rw [hv] at h
    refine (S1_mem_OmF D).2 ?_
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
    · exact G.pl.levelPlace_ne_basePlace t _ h hv
    · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
  intro hn
  apply hchi
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t / SqNum.nuH G t i j := by
    rw [SqNum.nuH, div_div_cancel]
  rw [e, div_eq_mul_inv]
  exact (hmu.mul hxi).mul hn.inv

end GlobalTheory.ThetaGridRamifiedOverBasePlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitFullyUnr

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ramificationIdx_eq_one_of_splitsFully (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) (q : Ideal (𝓞 E)) (hq : q ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E)) :
    q.ramificationIdx ℤ = 1 := by
  classical
  set P : Ideal ℤ := v.asIdeal.under ℤ with hP
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (P.primesOver (𝓞 E)).Finite := Set.finite_of_ncard_pos (by rw [h]; exact hn)
  letI : Fintype (P.primesOver (𝓞 E)) := hfin.fintype
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; exact h
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  have hpos : ∀ r ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      (fun _ => 1) r ≤ r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := fun r _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by rw [← Fintype.card_eq_sum_ones, hcard, hsum])
  have hm := (hall ⟨q, hq⟩ (Finset.mem_univ _)).symm
  exact Nat.eq_one_of_mul_eq_one_right hm

theorem under_eq_span_of_mem (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hq := Nat.absNorm_under_prime w.asIdeal
  have hd : (Ideal.absNorm (w.asIdeal.under ℤ) : ℤ) ∣ (p : ℤ) := by
    rw [← Int.cast_mem_ideal_iff]; simpa using hw
  have he : Ideal.absNorm (w.asIdeal.under ℤ) = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd)
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), he]

theorem not_mem_sq_of_ramificationIdx {p : ℕ} (hl : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (he : w.asIdeal.ramificationIdx ℤ = 1) :
    ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := w.isPrime
  have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  intro hsq
  have hne : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) w.asIdeal ≠ 1 := by
    rw [Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le]; simpa using hsq
  exact hne he

theorem not_le_differentIdeal (v : HeightOneSpectrum (𝓞 F)) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) :
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set p := Ideal.absNorm (v.asIdeal.under ℤ) with hpdef
  have hp : p.Prime := Nat.absNorm_under_prime v.asIdeal
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem v.asIdeal
  have hP : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  have hE : ∀ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal → ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
    intro w hw
    have hmem : w.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E) :=
      ⟨w.isPrime, ⟨by rw [hP, under_eq_span_of_mem w hp hw]⟩⟩
    exact not_mem_sq_of_ramificationIdx hp w hw (ramificationIdx_eq_one_of_splitsFully v h _ hmem)
  have hnd := GlobalTheory.SplitUnram.not_dvd_different hp v hpv (GlobalTheory.SplitUnram.not_mem_sq_of_ext hE v)
  exact fun hle => hnd (Ideal.dvd_iff_le.2 hle)

end GlobalTheory.SplitFullyUnr

theorem GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  intro D T L sc G W v hv
  exact GlobalTheory.BaseGoodPlace.psiUnr_of_not_le W.ψ_std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.exists_goodPlace_translateCombination_latticeIndicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∃ k : H, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧
        ι φ₁ = omB ν α g 1 (ι φ))
    {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (hSB : ∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) (h₀ : ∀ k, φ k B.v₁ = φ₀)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  first | exact @GlobalTheory.CombAtGood.exists_comb_translates_mem_So | exact GlobalTheory.CombAtGood.exists_comb_translates_mem_So | (intros; apply GlobalTheory.CombAtGood.exists_comb_translates_mem_So <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LatFill
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_smul {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

theorem piW_inclR {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

variable {n d : ℕ}

def fillSet (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) :
    AddSubgroup (Matrix (Fin n) (Fin d) (Fv F v)) where
  carrier := {M | ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = 0) ∧ ∀ i j, piW t (γ i j) = M i j}
  zero_mem' := ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
    exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1'], fun i j => by simp [h2, h2']⟩
  neg_mem' := by
    rintro _ ⟨γ, hγ, h1, h2⟩
    exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} {v : Pl (F := F)} {t : E →ₐ[F] Fv F v}

theorem smul_mem_fillSet {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hM : M ∈ fillSet σ X W v t) : a • M ∈ fillSet σ X W v t := by
  obtain ⟨γ, hγ, h1, h2⟩ := hM
  refine ⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.smul_apply, piW_smul, h1, mul_zero]
  · rw [Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]

theorem gen_mem_fillSet (h : IsCMExt F E σ) {x : Fin n → E} (hx : x ∈ X.L) {x' : Fin d → E} (hx' : x' ∈ W.L) :
    Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) ∈ fillSet σ X W v t := by
  have key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j)) := by
    intro e he
    refine intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩ ?_ ?_ he
    · have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
      refine ⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha,
          _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        simp only [AlgHom.comp_apply]
        ring
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        ring
    · rintro y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
      exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul],
        fun i j => by simp [h2, h2', add_mul]⟩
    · rintro y ⟨γ, hγ, h1, h2⟩
      exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩
  obtain ⟨γ, hγ, h1, h2⟩ := key _ (splitIdem_mem h t)
  exact ⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩

theorem vecMulVec_mem_fillSet (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v)
    {y' : Fin d → Fv F v ⊗[F] E} (hy' : y' ∈ latLoc F W.L v) :
    Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t := by
  refine latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t)
    (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · refine latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈
      fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'
    · have e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) =
          (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) := by
        ext i j; simp [splitVec, Matrix.vecMulVec_apply]; ring
      rw [e]
      exact smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')
    · convert zero_mem (fillSet σ X W v t) using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
    · convert add_mem hy hz using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply, mul_add]
    · convert neg_mem hy using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert zero_mem (fillSet σ X W v t) using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert add_mem hy hz using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply, add_mul]
  · convert neg_mem hy using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]

theorem mul_mul_transpose_eq_sum {K : Type} [Field K] (b : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin d) (Fin d) K)
    (A : Matrix (Fin n) (Fin d) K) :
    b * A * cᵀ = ∑ i, ∑ j, A i j • Matrix.vecMulVec (b *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LatFill

theorem GlobalTheory.LatFill.exists_latAtV_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  intro F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA
  have single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m),
      (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F := fun i k => by
    by_cases e : k = i
    · subst e; simp
    · simp [e]
  have hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t := by
    rw [GlobalTheory.LatFill.mul_mul_transpose_eq_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_
    obtain ⟨y, hy, ey⟩ := (hb _).1 (single_mem i)
    obtain ⟨y', hy', ey'⟩ := (hc _).1 (single_mem j)
    rw [← ey, ← ey']
    exact GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'
  obtain ⟨γ, hγ, h1, h2⟩ := hT
  refine ⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩
  have e : γ.map (piW t) = b.1 * A * c.1ᵀ := Matrix.ext fun i j => h2 i j
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl (F := F)) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

section Grp
variable {n : ℕ} {W : Spc F E n}

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}


variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

end Loc

end GlobalTheory.InertAvg
end
end
