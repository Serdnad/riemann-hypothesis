module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle028
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem pat_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (T : PAT H (Sp R)), (∃ (T' : PAT H (Sp R')) (_ : SABMap T'.t T.t (spMap f)), T'.g = T.g) ∧ ∀ (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), Nontrivial R' → T'.g = T.g ∧ IsPolFibre f T.pol T'.pol m.φ ∧ ∃ w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ), RigIso m w := by
  intro E _ _ _ H R R' _ _ f T
  refine ⟨?_, fun T' m hR => ?_⟩
  · obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) T.t
    obtain ⟨⟨T', ht, hg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    exact ⟨T', ht ▸ m, hg⟩
  · obtain ⟨-, e⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    have hd : SmoothOfRelativeDimension T.g T'.t.G.hom :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
    have hg : T'.g = T.g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ T'.dim hd (eSec T'.t.G p)
    obtain ⟨w, hw, hr, -⟩ := m.lin
    exact ⟨hg, ⟨hg, m.cart, e⟩, w, hw, hr⟩

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootNegDiscriminant_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have : (H.d : ℂ) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem cmHost_rootNegDiscriminant_ne_neg_self (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  apply cmHost_rootNegDiscriminant_ne_zero H
  linear_combination h / 2

theorem cmHost_conj_sqrtNegDisc (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h2 := H.sqrt_neg_disc_sq
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp [pow_two] at him hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem host_emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  rw [H.sqrt_neg_disc_sq]
  simpa using h

theorem host_mem_compl_psiSet (H : Host E) (τ : E →+* ℂ) :
    τ ∈ (psiSet H)ᶜ ↔ τ (H.rt : E) = -H.rt0 := by
  change ¬ (τ (H.rt : E) = H.rt0) ↔ _
  constructor
  · intro h
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 (host_emb_rt_sq H τ)).resolve_left h
  · intro h h'
    exact cmHost_rootNegDiscriminant_ne_neg_self H (h'.symm.trans h)

theorem card_psiSet_eq_card_compl (H : Host E) :
    Nat.card (psiSet H) = Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) := by
  refine Nat.card_congr
    { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      left_inv := fun τ => Subtype.ext (star_star τ.1)
      right_inv := fun τ => Subtype.ext (star_star τ.1) }
  · rw [host_mem_compl_psiSet, ComplexEmbedding.conjugate_coe_eq, ← cmHost_conj_sqrtNegDisc]
    exact congrArg _ τ.2
  · have h := (host_mem_compl_psiSet H τ.1).1 τ.2
    change _ = H.rt0
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, cmHost_conj_sqrtNegDisc, neg_neg]

theorem card_psiSet (H : Host E) : Nat.card (psiSet H) = Module.finrank ℚ E / 2 := by
  have h1 := Set.ncard_add_ncard_compl (psiSet H)
  have h2 := card_psiSet_eq_card_compl H
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [Nat.card_eq_fintype_card, Embeddings.card E ℂ] at h1
  rw [Nat.card_coe_set_eq]
  omega

variable {H : Host E} {l : Level H}

theorem labK_eq_iff (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (τ : E →+* ℂ) (a : E) (x : c.F) :
    labK c K τ a = algebraMap c.F K x ↔ τ a = (x : ℂ) := by
  change algebraMap c.F K (Formalism.L2.Pj.embF c τ a) = _ ↔ _
  rw [(algebraMap c.F K).injective.eq_iff, Subtype.ext_iff]
  rfl

theorem labK_injective (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] : Function.Injective (labK c K) := by
  intro τ τ' h
  refine RingHom.ext fun a => ?_
  exact (labK_eq_iff c K τ a (Formalism.L2.Pj.embF c τ' a)).1 (DFunLike.congr_fun h a)

theorem labK_bijective (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] :
    Function.Bijective (labK c K) := by
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  refine (labK_injective c K).bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card E ℂ]
  exact card_ringHom_le_finrank

end

theorem labK_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K], Function.Bijective (labK c K) ∧ Splits E K ∧ (∀ τ, ∃ t : 𝓞 E →+* 𝓞 K, ∀ a : 𝓞 E, (t a : K) = labK c K τ (a : E)) ∧ ∃ ρ : 𝓞 K, ρ ^ 2 = -(H.d : 𝓞 K) ∧ (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) ∧ (∀ τ, τ ∈ (psiSet H)ᶜ ↔ labK c K τ (H.rt : E) = ((-ρ : 𝓞 K) : K)) ∧ Nat.card (psiSet H) = Module.finrank ℚ E / 2 ∧ Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H l c K _ _ _
  have hb := labK_bijective c K
  refine ⟨hb, ?_, fun τ => ⟨RingOfIntegers.mapRingHom (labK c K τ), fun a => rfl⟩, ?_⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Embeddings.card E ℂ]
  let r : c.F := ⟨H.rt0, c.le (baseKA l).ρ.2⟩
  have hr : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [r] using H.sqrt_neg_disc_sq)
  have hK : (algebraMap c.F K r) ^ 2 = -(H.d : K) := by
    rw [← map_pow, hr]; simp
  have hint : IsIntegral ℤ (algebraMap c.F K r) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hK]
    exact (isIntegral_natCast H.d).neg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 K, algebraMap (𝓞 K) K ρ = algebraMap c.F K r := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨ρ, RingOfIntegers.ext ?_, fun τ => ?_, fun τ => ?_, card_psiSet H, ?_⟩
  · change algebraMap (𝓞 K) K (_ ^ 2) = algebraMap (𝓞 K) K (-_)
    rw [map_pow, map_neg, map_natCast, hρ]
    exact hK
  · change _ ↔ _ = algebraMap (𝓞 K) K ρ
    rw [hρ]
    exact (labK_eq_iff c K τ _ r).symm
  · rw [host_mem_compl_psiSet]
    have := (labK_eq_iff c K τ (H.rt : E) (-r)).symm
    rw [map_neg, ← hρ, ← map_neg] at this
    exact this
  · rw [← card_psiSet_eq_card_compl, card_psiSet]

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isModelAt : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  intro hT K _ _ A x φ hx p
  have hg : x.P.g = A.g := ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) A x φ).1 hx).1
  have hφ : IsGrpPullback x.P.A A.A (spMap (algebraMap (𝓞 K) K)) φ := hx.1
  let R := (p.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => p.valuation_le_one r
  have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
  obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := KeyPow.exists_keyIn_pullback hT f A (hg ▸ x.g_pos)
  have sq : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
  obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
      φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap (algebraMap R K)) φ' := hψ.cancel (hφ.congr hf.symm rfl) h₂
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq' : ∀ i, (spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left) ≫ y.P.A.hom =
      (epsR K).hom ≫ spMap (algebraMap R K) := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq' i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ' = spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left :=
    fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange (algebraMap R K) h y.basis hv'
  have e : y.P.g = x.P.g := hg₀.trans hg.symm
  obtain ⟨a, M, -, hM⟩ := KeyPow.exists_scalar_matrix hT x.P x.th x.th x.th_ne x.basis (hb e.symm)
  have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := by
    ext a <;> simp [Chart.dualMapR, Formalism.L2.Pj.dualMap]
  refine ⟨M, R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsFractionRing (p.valuation K).valuationSubring K), f, y, ψ, e, rfl,
    fun z => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩, ⟨hψ, w₀, (isGen_iff _).2 hw₀⟩,
    (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M _ x.basis hM).1 (hb e.symm)).ne_zero,
    fun k => ⟨_, hM k, ?_⟩⟩
  rw [hd, ← Category.assoc, hv', Category.assoc]

end GlobalTheory.LamF
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.ConjUnif

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem le_pull_id (x : Sp ℂ ⟶ A.left) (j : (L.pull (𝟙 A.left)).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull (𝟙 A.left)).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  rw [le_pull_iff, Category.comp_id]

def pullId (u : HolUnif A L g) : HolUnif A (L.pull (𝟙 A.left)) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j := u.fr (j PUnit.unit)
  fr_hol j := by
    have e : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (𝟙 A.left)).U j} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)} :=
      Set.ext fun z => le_pull_id _ j
    rw [e]
    exact u.fr_hol _
  fr_ne j z hz := u.fr_ne _ z ((le_pull_id _ j).1 hz)
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ z
      ((top_le_preimage_inf _ _ _).2 ⟨(le_pull_id _ j).1 hj, (le_pull_id _ j').1 hj'⟩)]
    congr 2

variable {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)

theorem cj_le (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : (L.pull ψ).ι) :
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ (L.pull ψ).U j ↔ ⊤ ≤ x.left ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_pull_iff L _ _ j).trans ?_
  rw [cjPt_comp]
  exact le_cj_iff _ _

def conjPull (u : HolUnif A L g) : HolUnif A' (L.pull ψ) g where
  ex := (cjUnif h (pullId u)).ex
  ex_add := (cjUnif h (pullId u)).ex_add
  ex_onto := (cjUnif h (pullId u)).ex_onto
  Λ := (cjUnif h (pullId u)).Λ
  ker := (cjUnif h (pullId u)).ker
  discrete := (cjUnif h (pullId u)).discrete
  full := (cjUnif h (pullId u)).full
  hol := (cjUnif h (pullId u)).hol
  fr j z := star (u.fr (j PUnit.unit) (star z))
  fr_hol j := by
    have e : {z | ⊤ ≤ ((cjUnif h (pullId u)).ex z).left ⁻¹ᵁ (L.pull ψ).U j} =
        {z | star z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)}} :=
      Set.ext fun z => cj_le h _ j
    rw [e]
    exact differentiableOn_star (u.hol _ 0).1 (u.fr_hol _)
  fr_ne j z hz := star_ne_zero.2 (u.fr_ne _ _ ((cj_le h _ j).1 hz))
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hm := (top_le_preimage_inf _ _ _).2 ⟨(cj_le h _ j).1 hj, (cj_le h _ j').1 hj'⟩
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ _ hm, star_mul']
    congr 1
    exact ((congrArg (fun x => valAt' x _ _) (cjPt_comp h (u.ex (star z)))).trans (val_cj _ _ _)).symm

theorem conjPull_isAH (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    (conjPull h u).IsAH (Hm.map star) fun l => star (χ ⟨star l.1, l.2⟩) := by
  have h0 : (pullId u).IsAH Hm χ :=
    ⟨hA.1, hA.2.1, hA.2.2.1, fun l j z hj => hA.2.2.2 l _ z ((le_pull_id _ j).1 hj)⟩
  have h1 := cj_isAH h _ h0
  exact ⟨h1.1, h1.2.1, h1.2.2.1, fun l j z hj =>
    h1.2.2.2 l j z ((cj_le_pull h _ j).2 ((le_pull_id _ j).2 ((cj_le h _ j).1 hj)))⟩

theorem exists_inv {X : Scheme.{0}} {M N : LB X} (w : LB.Iso M N) (hw : w.IsGen) :
    ∃ w' : LB.Iso N M, w'.IsGen ∧ ∀ (x : Sp ℂ ⟶ X) (j : N.ι) (i : M.ι), ⊤ ≤ x ⁻¹ᵁ (N.U j ⊓ M.U i) →
      valAt' x (M.U i ⊓ N.U j) (w'.s (i, j)).val = (valAt' x (N.U j ⊓ M.U i) (w.s (j, i)).val)⁻¹ := by
  have le : ∀ p : M.ι × N.ι, M.U p.1 ⊓ N.U p.2 ≤ N.U p.2 ⊓ M.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_, fun x j i hx => ?_⟩
  · have hm : (𝟙 X : X ⟶ X) y ∈ N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1) := ⟨le p hy.1, le q hy.2⟩
    have e := congrArg (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1))) (hw (p.2, p.1) (q.2, q.1))
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div M N (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
    have v : ∀ p : M.ι × N.ι, y ∈ M.U p.1 ⊓ N.U p.2 →
        gm (𝟙 X) y (M.U p.1 ⊓ N.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
        (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
    refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div N M (𝟙 X) y p q hy)
      ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
    rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (M.g p.1 q.1))]
    rfl
  · have hx' : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ N.U j) := by rwa [inf_comm]
    exact (valAt'_units_inv x hx' _).trans (congrArg _ (valAt'_res x (le (i, j)) _ hx'))

theorem exists_conj_unif : ∀ (x x' : KeyIn ℂ), KeyPB x' x (starRingEnd ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (starRingEnd ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (starRingEnd ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (starRingEnd ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (starRingEnd ℂ) (W i)) w' := by
  rintro x x' ⟨φ, he, w, hg', F, hφ, hw, hrig, hth, hF, hε, hv⟩ hg g u Hm χ θ Fd ⟨hA, hR, hθ, hFd⟩
  rw [KeyFibre.eq_dualMapR_of_algebraMap _ F hF hε] at hv
  obtain ⟨w', hw', hinv⟩ := exists_inv w hw
  have hP : (x.P.L.pull φ).IsLB := DVR.linComb_isLB x.P.L x.P.isLB _ _
  let u₁ := conjPull hφ u
  have me : MeasurableEmbedding (star : (Fin g → ℂ) → Fin g → ℂ) :=
    (starL' ℝ (A := Fin g → ℂ)).toHomeomorph.measurableEmbedding
  have fr : ∀ (j : x.P.L.ι) (i : x'.P.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) →
      valAt' (u₁.ex z).left ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) (w.s (fun _ => j, i)).val *
        (carry u₁ hP x'.P.isLB hw').fr i z = star (u.fr j (star z)) := by
    intro j i z hz
    obtain ⟨hj, hi⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hP x'.P.isLB hw' i (fun _ => j) z hi hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, i))) _
  refine ⟨carry u₁ hP x'.P.isLB hw', _, fun z => star (θ (star z)), star ⁻¹' Fd,
    carry_isAH hP x'.P.isLB hw' (conjPull_isAH hφ u hA), ?_, ?_, cj_domain hφ (pullId u) hFd, ?_, ?_⟩
  · intro i hi
    have h0 : (u₁.ex 0).left = eSec x'.P.A := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    have h0' : (u.ex 0).left = eSec x.P.A := by
      rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex 0).left
    have hi' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ x'.P.L.U (i PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hi hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi'⟩
    have e := fr (j PUnit.unit) (i PUnit.unit) 0 hz
    have hj' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U (j PUnit.unit) := by
      have := (cj_le hφ _ j).1 hj
      rwa [star_zero] at this
    rw [h0'] at hj'
    have hj'' : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => j PUnit.unit := fun p hp => mem_pull.2 (hj' hp)
    rw [star_zero, hR _ hj'', ← val_cj, Category.comp_id, h0] at e
    rw [h0] at hz
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _)
      (e.trans (val_rig he w x'.rig x.rig hrig (j PUnit.unit) (i PUnit.unit) hz))
  · intro i z hi
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi⟩
    have e := fr (j PUnit.unit) i z hz
    have e₁ := val_via w x.th x'.th hth (u₁.ex z).left (j PUnit.unit) i hz
    have e₂ : valAt' ((u₁.ex z).left ≫ φ) (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) =
        star (θ (star z)) * star (u.fr (j PUnit.unit) (star z)) :=
      (congrArg (fun x => valAt' x _ _) (cjPt_comp hφ (u.ex (star z)))).trans ((val_cj _ _ _).trans
        ((congrArg star (hθ _ (star z) ((cj_le hφ _ j).1 hj))).trans (star_mul' _ _)))
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, i))) ?_
    refine e₁.symm.trans (e₂.trans ?_)
    rw [← e]
    exact mul_left_comm _ _ _
  · rw [measurePreserving_star.measure_preimage_emb me Fd, ← measurePreserving_star.setIntegral_preimage_emb me _ Fd]
    refine congrArg (fun t : (Fin g → ℂ) → ℝ => (∫ z in star ⁻¹' Fd, t z) / (volume Fd).toReal) (funext fun z => ?_)
    rw [norm_star]
    exact congrArg (fun t : ℝ => ‖θ (star z)‖ ^ 2 * Real.exp (-Real.pi * t)) (hermSq_star Hm z)
  · intro cf v v' W h₁ h₂ hd
    have h₃ : ∀ (n : ℕ) (e : n = x.P.g), IsLieComb (fun i => cf (i.cast e)) (fun i : Fin n => x.v (i.cast e)) v := by
      rintro _ rfl
      exact h₁
    have e := (lieComb_baseChange ℂ ℂ _ _ _ φ hφ _ _ v _ x'.v v' hv (h₃ _ hg)).2 h₂
    exact cj_isDiff hφ (pullId u) (GlobalTheory.Reg.isTangent_of_isLieComb x.basis.1 h₁) e hd

end GlobalTheory.ConjUnif
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_natCast_pow {v : epsR R ⟶ G} (hv : IsTangent v) (n : ℕ) :
    IsLieComb ![(n : R)] ![v] (v ^ n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.2 hv
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    exact (lieMultiple_calculus R G G v _ v n 1).2.1 hv ih
      (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.1

theorem isMonHom_id_pow [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem quadratic_equation_of_derivative : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (W : P.A ⟶ P.A) (w : k) (n : ℕ), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom W → IsLieComb ![w] ![v] (v ≫ W) → w * w + n = w → (W ≫ W) * (𝟙 P.A) ^ n = W := by
  intro hT hB k _ s P v W w n hv hb hW hw heq
  have hc := P.isAb.comm
  have h1 := isMonHom_id_pow (G := P.A) n
  have h2 : IsMonHom ((W ≫ W) * (𝟙 P.A) ^ n) :=
    inferInstanceAs (IsMonHom (lift (W ≫ W) ((𝟙 P.A) ^ n) ≫ μ[P.A]))
  refine GlobalTheory.T.curve_hom_ext_of_derivative_lieBasis hT hB k s P P v _ _ hb h2 hW ?_
  have h3 : IsLieComb ![w] ![v ≫ W] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ v w w).2.2.2.1 W hw
  have h4 : IsLieComb ![w * w] ![v] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ _ w w).2.2.1 hw h3
  have h5 : IsLieComb ![w * w + n] ![v] (((v ≫ W) ≫ W) * v ^ n) :=
    (lieMultiple_calculus k P.A P.A v _ _ (w * w) n).2.1 hv h4 (isLieComb_natCast_pow hv n)
  rw [heq, isLieComb_one_iff_comp] at h5
  rw [isLieComb_one_iff_comp] at hw
  rw [MonObj.comp_mul, MonObj.comp_pow, Category.comp_id, ← Category.assoc, h5, ← hw]

end GlobalTheory.LieMultiple
end
end
