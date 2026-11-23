module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle169
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

end GlobalTheory.Mem.Per.ConjCM
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.CsdInf

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem star_expU (z : Cinf L) :
    Units.map (starRingEnd (Cinf L)).toMonoidHom (expU z) = expU (star z) :=
  Units.ext (funext fun w => by
    change starRingEnd ℂ (Complex.exp (z w)) = Complex.exp (star (z w))
    rw [← Complex.exp_conj]
    rfl)

theorem lie_iff (χ : HChar L) :
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  constructor
  · intro h u
    obtain ⟨z, rfl⟩ : ∃ z, expU z = u := ⟨_, expU_log u⟩
    rw [star_expU, ← expU_add]
    apply Units.ext
    have h1 := h z
    rw [map_neg] at h1
    rw [chiInf_expU, map_add (f := _), ← h1, neg_add_cancel, Complex.exp_zero, Units.val_one]
  · intro h z
    have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := h (expU (t • z))
      rw [star_expU, ← expU_add, star_smul, star_trivial, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add (f := _)] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

theorem inf_eq (χ : HChar L) (k : Lˣ) :
    χ.inf k = chiInf χ (Units.map (pInf L).toMonoidHom (diagUnits L k)) := by
  rw [HChar.inf, chiInf, MonoidHom.comp_apply, MonoidHom.comp_apply, NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem pInf_conj (k : Lˣ) :
    Units.map (pInf L).toMonoidHom (diagUnits L (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k)) =
      Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map (pInf L).toMonoidHom (diagUnits L k)) :=
  Units.ext (pInf_complexConj (k : L))

theorem field_iff (χ : HChar L) :
    (∀ k : Lˣ, χ.inf (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k) = (χ.inf k)⁻¹) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  classical
  constructor
  · intro h u
    let q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L := (pInf L).toMonoidHom.comp (incl ∅)
    have hq : Continuous q := (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)
    have h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1 :=
      fun y => (denseRange_units ∅).induction_on
        (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y
        (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul
          ((Continuous.units_map _ continuous_star).comp (hq.units_map _)))) continuous_const) fun k => by
        have e : Units.map q (Units.map (proj ∅) (diagUnits L k)) = Units.map (pInf L).toMonoidHom (diagUnits L k) := rfl
        rw [e, ← pInf_conj, map_mul, ← inf_eq, ← inf_eq, h k, mul_inv_cancel]
    have h3 := h2 (Units.map (proj ∅) (infId L u))
    have e : Units.map q (Units.map (proj ∅) (infId L u)) = u := Units.ext (by
      change (infEq L).symm (1 - infEq L 1 + infEq L u) = u
      simp)
    rwa [e] at h3
  · intro h k
    have h1 := h (Units.map (pInf L).toMonoidHom (diagUnits L k))
    rw [← pInf_conj, map_mul, ← inf_eq, ← inf_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1

end GlobalTheory.CuspRep.CsdInf


open GlobalTheory.CuspRep.CsdInf in
theorem GlobalTheory.CuspRep.csdInf_iff : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have e : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj H.E)).toMonoidHom k :=
    fun k => Units.ext (host_complexConj H k).symm
  show (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹
  simp only [e]
  exact (lie_iff χ).trans (field_iff χ).symm
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcris_eq_acris_localization_periodT : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), ∃ (r : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | exact GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | (intros; apply GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.unitaryDeterminantKernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (_root_.Neutral.B1.Ideles H.E)) ∧ (∀ w y, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, _root_.Neutral.B1.diagUnits H.E (_root_.Formalism.L2.Host.upF H.F k) ∈ KD H) ∧ ∀ χ : _root_.Formalism.L2.Host.HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ _root_.Formalism.L2.Host.OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  first | exact @GlobalTheory.Mem.KerDet.kernel_open_and_factor | exact GlobalTheory.Mem.KerDet.kernel_open_and_factor | (intros; apply GlobalTheory.Mem.KerDet.kernel_open_and_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  first | exact @GlobalTheory.ToricOverField.toric_section_eq_over_field | exact GlobalTheory.ToricOverField.toric_section_eq_over_field | (intros; apply GlobalTheory.ToricOverField.toric_section_eq_over_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.toricTorsionSection_eq_pushed_trait_point_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  first | exact @GlobalTheory.TorSecLocal.toric_torsion_section_overLocal | exact GlobalTheory.TorSecLocal.toric_torsion_section_overLocal | (intros; apply GlobalTheory.TorSecLocal.toric_torsion_section_overLocal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  first | exact @GlobalTheory.OscGauss.inner_omAct0_adjZ | exact GlobalTheory.OscGauss.inner_omAct0_adjZ | (intros; apply GlobalTheory.OscGauss.inner_omAct0_adjZ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.lawNorm_classSum_fock : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h [Fintype S.Cl], S.LawNorm emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.GStep.lawNorm | exact GlobalTheory.Mem.Col2.GStep.lawNorm | (intros; apply GlobalTheory.Mem.Col2.GStep.lawNorm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_integralForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  first | exact @GlobalTheory.Mem.Col2.DiaLat.dia_lat | exact GlobalTheory.Mem.Col2.DiaLat.dia_lat | (intros; apply GlobalTheory.Mem.Col2.DiaLat.dia_lat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_lawBasis : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.lawBasis_all | exact GlobalTheory.Mem.Col2.lawBasis_all | (intros; apply GlobalTheory.Mem.Col2.lawBasis_all <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_complexForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  first | exact @GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | exact GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | (intros; apply GlobalTheory.Mem.Col2.DiaStab.lawDiaStable <;> assumption)
end
