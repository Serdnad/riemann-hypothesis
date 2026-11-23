module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle242
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle379
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle036
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle371
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvOfPowEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOneOfLowerParab
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle382
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem resU_bij_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V V' : ObjectProperty C} (e : V = V') (k : V ≤ U) (k' : V' ≤ U) (n : ℕ)
    (h : Function.Bijective ((resU F k').pull n)) : Function.Bijective ((resU F k).pull n) := by
  subst e
  exact h

theorem kun_congr {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ : ObjectProperty E.C₂}
    {U₃ U₃' : ObjectProperty E.D} (e₁ : U₁ = U₁') (e₃ : U₃ = U₃')
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂ (E.L₂.obj T))
    (h : E.Kun U₁ U₂ U₃ h₁ h₂) : E.Kun U₁' U₂ U₃' h₁' h₂' := by
  subst e₁ e₃
  exact h

theorem glue_top (hMV : MVBij) (hCD : CovDesc) {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁)
    (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D) {ι : Type} [DecidableEq ι] [Fintype ι]
    (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α, Cosieve (W α))
    (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T))
    (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T))
    (hK : ∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S))
    (k₁ : capU V ∅ ≤ U₁) (k₃ : capU W ∅ ≤ U₃)
    (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n))
    (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n))
    (g₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (g₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : E.Kun U₁ U₂ U₃ g₁ g₂ :=
  (GlobalTheory.T.kuenneth_of_restrict_bijective E g₁ g₂ (h₁ ∅) (h₂ ∅) k₁ (le_refl U₂) k₃ b₁ (fun a n => resU_self_bij _ _ _ n) b₃).2
    (GlobalTheory.T.kuenneth_mayer_vietoris_right hMV hCD E U₂ V W hV hW h₁ h₂ hK)

section Site

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem inU_pull (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {r : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z)
    (hu : u ≫ q = r) (A : Z.Opens) (T) : inU r (u ⁻¹ᵁ A) T ↔ inU q A ((smS u hu).G.obj T) := by
  subst hu
  exact (hS K Z Z Y q (𝟙 Z) u).2.2.2.2.1 A T

theorem inU_cos (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A : Z.Opens) : Cosieve (inU q A) :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).1 A

theorem inU_top (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (T) : inU q ⊤ T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.1 T

theorem inU_inf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A B : Z.Opens) (T) :
    inU q (A ⊓ B) T ↔ inU q A T ∧ inU q B T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.2.1 A B T

theorem inU_biInf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} [DecidableEq ι] (A : ι → Z.Opens)
    (S : Finset ι) (T) : inU q (⨅ α ∈ S, A α) T ↔ ∀ α ∈ S, inU q (A α) T := by
  induction S using Finset.induction_on with
  | empty => simpa using inU_top hS q T
  | insert a S _ ih =>
    rw [Finset.iInf_insert, inU_inf hS, ih]
    simp

end Site

theorem kun_left : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hS hMV hCD hZ hA hKA K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP g₁ g₂
  classical
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hw := hP.w.symm
  have inP : ∀ (A : X.Opens) (B : X'.Opens) (T),
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ A ⊓ p₂ ⁻¹ᵁ B) T ↔
        inU q A ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) ∧ inU q' B ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) := by
    intro A B T
    rw [inU_inf hS, inU_pull hS q p₁ rfl, inU_pull hS q' p₂ hw]
    rfl
  let V : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).C₁ := fun α => inU q (U.U α)
  let W : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤)
  have h₁ : ∀ S : Finset U.ι, ∀ T, capU W S T → capU V S ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, h⟩
    exact ⟨⟨α, ((inP _ _ T).1 hα).1⟩, fun β hβ => ((inP _ _ T).1 (h β hβ)).1⟩
  have h₂ : ∀ S : Finset U.ι, ∀ T, capU W S T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) :=
    fun S T _ => inU_top hS q' _
  have eV : ∀ S : Finset U.ι, S.Nonempty → inU q (⨅ α ∈ S, U.U α) = capU V S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inU_biInf hS q U.U S T).trans ⟨fun h => ⟨⟨α₀, h α₀ h₀⟩, h⟩, fun h => h.2⟩)
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ (⨅ α ∈ S, U.U α) ⊓ p₂ ⁻¹ᵁ ⊤) = capU W S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inP _ _ T).trans ⟨fun h => ?_, fun h => ?_⟩)
    · have a : ∀ α ∈ S, W α T := fun α hα =>
        (inP _ _ T).2 ⟨(inU_biInf hS q U.U S _).1 h.1 α hα, h.2⟩
      exact ⟨⟨α₀, a α₀ h₀⟩, a⟩
    · exact ⟨(inU_biInf hS q U.U S _).2 fun α hα => ((inP _ _ T).1 (h.2 α hα)).1, inU_top hS q' _⟩
  have hK : ∀ S : Finset U.ι, S.Nonempty →
      (hodgeXD q q' p₁ p₂ hw).Kun (capU V S) (inU q' ⊤) (capU W S) (h₁ S) (h₂ S) := by
    intro S hSn
    obtain ⟨α₀, h₀⟩ := id hSn
    obtain ⟨c, -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hSn)
    exact kun_congr _ (eV S hSn) (eW S hSn) _ _ _ _
      (GlobalTheory.T.kuenneth_product_local_global hS hMV hCD hZ hA hKA K X X' P q q' p₁ p₂ hP _ _ ⟨c⟩
        (fun T h => ((inP _ _ T).1 h).1) (fun T h => ((inP _ _ T).1 h).2))
  have e₁ : capU V ∅ = fun T => ∃ α, inU q (U.U α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have e₃ : capU W ∅ = fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have k₁ : capU V ∅ ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have k₃ : capU W ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  have hc : (⨆ α, p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) = p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ := by
    refine le_antisymm (iSup_le fun α => inf_le_inf_right _ ((TopologicalSpace.Opens.map p₁.base).monotone le_top)) ?_
    intro x _
    have hx : p₁ x ∈ (⨆ α, U.U α) := by
      rw [U.cover]
      trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα, trivial⟩
  have l₁ : (fun T => ∃ α, inU q (U.U α) T) ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have l₃ : (fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T) ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨α, hα⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  exact glue_top hMV hCD (hodgeXD q q' p₁ p₂ hw) (inU q ⊤) (inU q' ⊤) _ V W
    (fun α => inU_cos hS q _) (fun α => inU_cos hS _ _) h₁ h₂ hK k₁ k₃
    (fun a n => resU_bij_congr _ e₁ k₁ l₁ n (hZ K X q U.ι ⊤ U.U U.cover l₁ a n))
    (fun a n => resU_bij_congr _ e₃ k₃ l₃ n (hZ K P (p₁ ≫ q) U.ι _ _ hc l₃ a n)) g₁ g₂

end GlobalTheory.CompanionTheory.KunGlue
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality

theorem eqOn_compl_one {H R : ℂ → ℂ} (hH : DifferentiableOn ℂ H {1}ᶜ) (hR : DifferentiableOn ℂ R {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → H s = R s) : Set.EqOn H R {1}ᶜ := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff]; norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by norm_num)
  exact (hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)

theorem coneWeight_int {F : Type} [Field F] [NumberField F] {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F)
    (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ∃ z : ℤ, coneWeight l A y v m = z := by
  unfold coneWeight
  split_ifs
  · exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩

theorem exists_pow_mul_sum {J : Type} (S : Finset J) (l : ℕ) (q : J → ℚ) (K : J → ℕ) (z : J → ℤ)
    (h : ∀ j, (l : ℚ) ^ K j * q j = z j) : ∃ (K' : ℕ) (Z : ℤ), (l : ℚ) ^ K' * ∑ j ∈ S, q j = Z := by
  refine ⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hle : K j ≤ ∑ i ∈ S, K i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem padicValRat_int_div_nonneg (l : ℕ) [Fact l.Prime] (Z : ℤ) (D : ℕ) (hD : D ≠ 0) (h : ¬ l ∣ D) :
    0 ≤ padicValRat l ((Z : ℚ) / (D : ℚ)) := by
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hZ' : (Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  rw [padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

theorem classTwist_value_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk
  obtain ⟨hb, hy, hvv, hr, e, he⟩ := hP
  letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm
  set l := Ideal.absNorm 𝔠 with hl_def
  have hl0 : 0 < l := hN.pos
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F)]
    convert NumberField.Embeddings.card F ℂ
  have hNb : Ideal.absNorm 𝔟 ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNb
  have hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j)) := fun j =>
    goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)
  have hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) *
        coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s)) := by
    intro j
    obtain ⟨Tj, hd, hs, -⟩ := abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F))
      (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0
      (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)
    exact ⟨Tj, hd, hs⟩
  choose Tc hTcd hTcs using hcont
  have key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)),
      (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2) := by
    rintro s ⟨j, m⟩
    dsimp only
    have hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m} := he ⟨j, m⟩
    have hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m := by
      unfold classWeight coneWeight
      rw [le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]
    have hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) =
        Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟 := by rw [← hx, map_mul]
    rw [hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s),
      mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s := by
    intro s hs
    have h1 := (e.hasSum_iff.mpr (hS s hs))
    have h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s *
        ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s) := by
      convert h1 using 1
      funext p
      exact (key s p).symm
    have h3 := h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))
    rw [Finset.mul_sum]
    exact h3.unique (hasSum_fintype _)
  have hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact differentiableAt_id.const_cpow (Or.inl hNbC)
    · have hsd := DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)
      have hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j := by
        funext t
        simp [Finset.sum_apply]
      rw [hfun]
      exact hsd
  have heq := eqOn_compl_one hT hRd (fun s hs => hRs s hs)
  have hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z := by
    intro j
    refine GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F))
      (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ)
      (fun σ => (hy j).2 σ) (hw j) (fun m => coneWeight_int l _ _ _ m) (Tc j) (hTcd j).differentiableOn
      (hTcs j) (k - 1) (fun m => ?_)
    have h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) =
        ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ) := by
      rw [← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]
      exact Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm
    refine ⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩
    try beta_reduce
    rw [Finset.prod_pow, h1]
    first | norm_cast | (push_cast; ring) | simp
  choose qj Kj zj hqj hzj using hint
  obtain ⟨K', Z, hZ⟩ := exists_pow_mul_sum Finset.univ l qj Kj zj hzj
  have hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ) := by rw [Nat.cast_sub hk]; push_cast; ring
  have hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)
  have hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ) := by
    rw [heq hmem]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs0]; exact hqj j
  have hlK : (l : ℚ) ^ K' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')
  have hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K' := by
    rw [eq_div_iff hlK, mul_comm]; exact hZ
  have hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)
  refine ⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩
  · rw [hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]
    push_cast
    ring
  · intro l' hl' hne hndvd
    haveI := Fact.mk hl'
    apply padicValRat_int_div_nonneg l' Z _ hD
    intro hdvd
    rcases (Nat.Prime.dvd_mul hl').mp hdvd with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))
    · exact hndvd (hl'.dvd_of_dvd_pow h)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SegExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow_nat (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]

theorem norm_absPow_nat (n : ℕ) (u : kˣ) : ‖((absPow k ((n : ℕ) : ℂ) u : ℂˣ) : ℂ)‖ = nabs k u ^ n := by
  have h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; rfl
  rw [h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _),
    Real.rpow_natCast]

theorem cast_tri (l : ℕ) (hl : 0 < l) : (((l * (l - 1) / 2 : ℕ)) : ℝ) = (l : ℝ) * ((l : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ l * (l - 1) := (Nat.even_mul_pred_self l).two_dvd
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]
  norm_num

theorem exponent_lseg (Δ : Segment k) (y : IrrGL (k := k)) (s e : ℝ) (t : kˣ) (c : ℂ) (ht : nabs k t < 1)
    (hL : IsLSeg Δ y.rep) (hc : Zl.ScalarBy Δ.first t c) (hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e))
    (hy : ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) :
    s = e + ((Δ.len : ℝ) - 1) / 2 := by
  have h1 := GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc
  have h2 := hy t _ h1
  have hdeg : y.1 = Δ.len * Δ.d := hL.deg_eq.symm
  have hα : 0 < nabs k t := nabs_pos' k t
  have hlog : Real.log (nabs k t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hα ht.ne
  rw [norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le,
    ← Real.rpow_add hα] at h2
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow hα, Real.log_rpow hα] at h3
  have h4 := mul_right_cancel₀ hlog h3
  rw [cast_tri _ Δ.len_pos, hdeg] at h4
  have hl : (0 : ℝ) < Δ.len := by exact_mod_cast Δ.len_pos
  have hd : (0 : ℝ) < Δ.d := by exact_mod_cast Δ.d_pos
  push_cast at h4
  have h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0 := by linear_combination -h4
  have h6 := (mul_eq_zero.1 h5).resolve_left (by positivity)
  linarith

theorem len_lt_of_precedes {Δ Δ' : Segment k} {j : ℕ} (hl : Δ.Linked Δ') (hf : Δ'.first = Δ.first.nu j) :
    Δ.len < j + Δ'.len := by
  by_contra hcon
  refine hl.2.2 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
  refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
  rw [hf, IrrGL.nu_nu]
  push_cast
  rfl

theorem exponent_lt_of_precedes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  intro k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP
  obtain ⟨hlink, j, hj, hf⟩ := hP
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hα1 : nabs k t < 1 := GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have hα : 0 < nabs k t := nabs_pos' k t
  obtain ⟨e, he⟩ := GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.central_character_exists k Δ.first t
  have hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e) := he t c hc
  have hdd : Δ'.d = Δ.d := congrArg Sigma.fst hf
  have hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)) := by
    rw [hf]
    exact GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc
  have hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((Δ'.d : ℝ) * (e + j)) := by
    rw [norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_add hα]
    congr 1
    show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _
    ring
  have h1 := exponent_lseg Δ y s e t c hα1 hL hc hcn hy
  have h2 := exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'
  have h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast len_lt_of_precedes hlink hf
  have h4 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [h1, h2]
  linarith

end GlobalTheory.CompanionTheory.SegExp
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.phi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.phiGP | exact GlobalTheory.CompanionTheory.LeibPhi.phiGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.phiGP <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.Contraction

theorem e1 : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  intro k _ _ _ _ N J θ l t hA hT g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hθJ : J.map θ.toMonoidHom = J := hA.2.2.2.2.2.2.1
  have hθa : θ a ∈ J := by
    rw [← hθJ]
    exact Subgroup.mem_map_of_mem _ ha
  obtain ⟨j₁, hj₁, n, hn, τ, hτ, h₁⟩ :=
    GlobalTheory.CompanionTheory.LbcKillN.killN N J θ l t hA hT (b * θ a) (J.mul_mem hb hθa)
  obtain ⟨j₂, hj₂, κ, hκ, h₂⟩ := GlobalTheory.CompanionTheory.Lbc.KillNlo.killNlo N J θ l t hA hT n hn τ hτ
  refine ⟨(a * j₁ * j₂)⁻¹, J.inv_mem (J.mul_mem (J.mul_mem ha hj₁) hj₂), κ, hκ, ?_⟩
  rw [← h₂, ← h₁]
  simp only [inv_inv, map_inv, map_mul]
  group

end GlobalTheory.CompanionTheory.Lbc.Contraction
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.dominant_iwahori_coset_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps <;> assumption)
end
