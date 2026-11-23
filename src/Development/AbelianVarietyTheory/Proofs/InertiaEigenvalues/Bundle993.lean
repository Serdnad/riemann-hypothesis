module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle946
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle550
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle037
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle742
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle950
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle947
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle992
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle210
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle952
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle930
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGalois

theorem fieldRange_of_normal (L : IntermediateField ℚ ℂ) [hN : Normal ℚ L] (f : L →+* ℂ) :
    f.toRatAlgHom.fieldRange = L :=
  @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ L (by convert hN) f.toRatAlgHom

theorem exists_goodCover_galois (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hJ : LawsJ T) (i : Fin D.R.m) (hj : InR D ((i : ℕ) + 1)) (n pd : ℕ) (I : Ideal (𝓞 D.host.E))
    (haux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd)
    (hK : I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}})
    (hprod : I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)})
    (hsup : I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hle : T.Q.c.F ≤ L)
    (hz : zeta (T.Q.l.M * pd) ∈ L) (hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i (L.val : L →+* ℂ))
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * pd) L.toSubfield) :
    ∃ C : Cover T ((i : ℕ) + 1) T.σ₀, C.d.pd = pd ∧ C.d.I = I ∧ C.σ₂.fieldRange = L.toSubfield ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T R i C n := by
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨hodd, -, -, hcop, -⟩ := id haux
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hJ.toLawsM.pins
  have hA : T.Q.l.A = 1 := hnum.2.1
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := hnum.2.2.2.2.2.2 _ hj; omega
  obtain ⟨l₂, hd, hM, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ T.Q.H T.Q.l).1 pd I hodd hcop hK hprod hsup
  obtain ⟨Xo₂⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) l₂ hpq
  let c' : Coeff T.Q.l :=
    { F := L, fin := inferInstance, conj := fun τ a => hle (T.Q.c.conj τ a)
      zeta_mem := hle T.Q.c.zeta_mem, le := T.Q.c.le.trans hle }
  have hM' : l₂.M' = T.Q.l.M * pd := by
    rw [Level.M', hA₂, hA, hM, Nat.lcm_one_right]
  let c₂ : Coeff l₂ :=
    { F := c'.F, fin := c'.fin, conj := c'.conj
      zeta_mem := by rw [hM']; exact hz
      le := by have h := c'.le; unfold KA at h ⊢; rw [hA₂]; exact h }
  obtain ⟨d, hdpd, hdI, hdl, -, -, -, hlev, -⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l
    (T.Q.Xo ((i : ℕ) + 1)) c' hpq 0 pd I l₂ Xo₂ c₂ rfl hd hM hcop hMb hsup
  obtain ⟨σ', hσ'⟩ := GlobalTheory.CoverExists.exists_ext_of_le (K := T.Q.c.F) (L := L) hle T.σ₀
  let σ₂ : d.c₂.F →+* ℂ := σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)
  have hσ₂ : σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = T.σ₀ := by
    rw [← hσ']; ext x; simp [σ₂, incF]
  have hA1 : d.l₂.A = 1 := by rw [hdl, hA₂, hA]
  obtain ⟨U₂, dict₂, hU⟩ := GlobalTheory.T.exists_levelCover_uniformisation_dictionary D T hJ _ hj T.σ₀ hσ c' hle d σ₂ hlev hA1 hσ₂

  have hrange : (σ'.toRatAlgHom).fieldRange = L := fieldRange_of_normal L σ'
  have hsurj : ∀ y : L, ∃ z : d.c₂.F, σ₂ z = (y : ℂ) := by
    intro y
    have hy : (y : ℂ) ∈ (σ'.toRatAlgHom).fieldRange := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hy
    exact ⟨d.eF x, by simp [σ₂, ← hx]⟩
  have hfr : σ₂.fieldRange = L.toSubfield := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have : σ' (d.eF.symm z) ∈ (σ'.toRatAlgHom).fieldRange := AlgHom.mem_fieldRange.2 ⟨_, rfl⟩
      rw [hrange] at this
      exact this
    · intro hx
      obtain ⟨z, hz'⟩ := hsurj ⟨x, hx⟩
      exact ⟨z, hz'⟩
  have hsm₂ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i σ₂ := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hsm.1 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
    · obtain ⟨y, hy⟩ := hsm.2 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
  let C₀ : Cover T ((i : ℕ) + 1) T.σ₀ := ⟨c', hle, d, σ₂, U₂, dict₂, fun _ => 1⟩
  have hdom : ∀ m, Even m → Dom (0 : (D.host.E →+* ℂ) × ℕ → ℕ) m := fun m hm =>
    ⟨fun _ _ _ _ => le_rfl, hm⟩
  have hauxd : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M d.pd := hdpd ▸ haux
  by_cases hn : Even n
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) n
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, hcc, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) 0
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, fun a ha => absurd ha.2 hn, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray

end GlobalTheory.CoverGalois
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescGlue

open GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

theorem finite_of_overPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (hl : l.Prime)
    (S : Set (HeightOneSpectrum (𝓞 L))) (h : OverPrime l S) : S.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  show la.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact h la hla

theorem finite_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : S.Finite) : (below φ S).Finite := by
  have e : below φ S = ⋃ la ∈ S, {p : HeightOneSpectrum (𝓞 K) |
      p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)} := by
    ext p; simp [below]
  rw [e]
  exact hS.biUnion fun la _ => Set.Subsingleton.finite fun p1 h1 p2 h2 =>
    HeightOneSpectrum.ext (h1.trans h2.symm)



theorem glue : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT h1 h2 h3 h4 h5 h6 i hVS hV hFP l hl C hC hPin S hS hUn φ hφmem hKf
    m x ψ hψ hφ hloc
  classical
  have hσ : ∀ t : T.Q.c.F, C.σ₂ (C.inc t) = T.σ₀ t := fun t => by
    rw [← RingHom.comp_apply, hC.1.2.2.1]
  have hfin : S.Finite := finite_of_overPrime l hl S hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    refine ⟨m, fun a => C.σ₂ (x a), ψ, fun a => ⟨x a, rfl, fun la h => absurd h (Set.notMem_empty la)⟩,
      fun a => ?_, hφ⟩
    obtain ⟨f, ⟨hf1, hf2⟩, hf⟩ := hψ a
    exact ⟨f, ⟨hf1, hf2, fun p hp => by
      obtain ⟨la, hla, _⟩ := hp
      exact absurd hla (Set.notMem_empty la)⟩, hf⟩
  set S' := hfin.toFinset with hS'
  have hmem : ∀ la : S', la.1 ∈ S := fun la => hfin.mem_toFinset.1 la.2
  choose m' x' ψ' hx' hψ' hφ' using fun la : S' => hloc la.1 (hmem la)
  choose a' ha' hav using fun (la : S') (a : Fin (m' la)) => hx' la a
  have hset : ∀ la : S', below C.inc {la.1} =
      {p | p.asIdeal = la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc)} := fun la => by
    ext p; simp [below]
  choose t ht htψ using fun (la : S') (a : Fin (m' la)) =>
    GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places D T hT i (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs h6.kap i)
      (la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc))
      (Ideal.IsPrime.comap _ (hK := la.1.isPrime)) (below C.inc S) (finite_below C.inc hfin) (ψ' la a)
      (hset la ▸ hψ' la a)
  have hte : ∀ (la : S') (a : Fin (m' la)), la.1.valuation _ (C.inc (t la a : T.Q.c.F)) = 1 := fun la a => by
    have e : C.inc (t la a : T.Q.c.F) = ((RingOfIntegers.mapRingHom C.inc (t la a) : 𝓞 C.d.c₂.F) : C.d.c₂.F) := rfl
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem la.1).mpr fun h => ht la a (Ideal.mem_comap.2 h)
  have ht0 : ∀ (la : S') (a : Fin (m' la)), T.σ₀ (t la a : T.Q.c.F) ≠ 0 := fun la a => by
    refine (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    rintro h0
    exact ht la a (h0 ▸ Ideal.zero_mem _)
  let Y : S' → Finset C.d.c₂.F := fun la => Finset.univ.image fun a => a' la a / C.inc (t la a : T.Q.c.F)
  have hY : ∀ la, ∀ y ∈ Y la, la.1.valuation _ y ≤ 1 := by
    intro la y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    rw [map_div₀, hte, div_one]
    exact hav la a la.1 (Set.mem_singleton _)
  have hne : S'.Nonempty := by
    obtain ⟨la, h⟩ := hSne
    exact ⟨la, hfin.mem_toFinset.2 h⟩
  obtain ⟨e, he1, he⟩ := GlobalTheory.exists_partition_one_integral_at_places _ S' hne Y hY
  let ι := Σ la : S', Fin (m' la)
  let ε := Fintype.equivFin ι
  let X : ι → ℂ := fun s => C.σ₂ (e s.1 * (a' s.1 s.2 / C.inc (t s.1 s.2 : T.Q.c.F)))
  let Ψ : ι → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ) := fun s => T.σ₀ (t s.1 s.2 : T.Q.c.F) • ψ' s.1 s.2
  have key : ∀ s : ι, X s • Ψ s = C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := by
    intro s
    simp only [X, Ψ, smul_smul, map_mul, map_div₀, hσ, ha']
    congr 1
    field_simp [ht0 s.1 s.2]
  refine ⟨Fintype.card ι, fun k => X (ε.symm k), fun k => Ψ (ε.symm k), fun k => ⟨_, rfl, fun la'' h'' =>
    he _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) la'' (hfin.mem_toFinset.2 h'')⟩,
    fun k => htψ _ _, ?_⟩
  symm
  calc ∑ k, X (ε.symm k) • Ψ (ε.symm k) = ∑ s : ι, X s • Ψ s := Equiv.sum_comp ε.symm (fun s => X s • Ψ s)
    _ = ∑ s : ι, C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := Finset.sum_congr rfl fun s _ => key s
    _ = ∑ la : S', ∑ a : Fin (m' la), C.σ₂ (e la) • (x' la a • ψ' la a) := Fintype.sum_sigma _
    _ = ∑ la : S', C.σ₂ (e la) • φ := Finset.sum_congr rfl fun la _ => by rw [← Finset.smul_sum, ← hφ' la]
    _ = φ := by rw [← Finset.sum_smul, ← map_sum, he1, map_one, one_smul]

end GlobalTheory.DescGlue
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_one_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescLoc.desc_loc | exact GlobalTheory.DescLoc.desc_loc | (intros; apply GlobalTheory.DescLoc.desc_loc <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

noncomputable section

namespace GlobalTheory.TraceIdem

theorem nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [nval]
  rw [nval_of_ne hz, EReal.coe_nonneg]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_nonneg_iff]
  have h1 : valV T.V z ≠ 0 := valV_ne_zero hz
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h' : 0 ≤ vV T.V z := by exact_mod_cast h
      unfold vV at h'
      rw [← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]; omega
    · linarith
  · intro h
    left
    refine ⟨?_, he'.le⟩
    have := (WithZero.log_le_log h1 one_ne_zero).2 h
    rw [WithZero.log_one] at this
    have h' : 0 ≤ vV T.V z := by unfold vV; omega
    exact_mod_cast h'

theorem trace_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  intro D T hL j hj σ hσ a n hD hspan hmu C hU hP la p hla m β hβ hβi y hφ
  obtain ⟨g, hgs, hgp, hgi⟩ := (GlobalTheory.T.exists_integral_cover_form_pullback_combination D T hL j hj σ hσ a n hD C hU hP la m β (fun k => (hβ k).1) y hφ)
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  obtain ⟨N, hN⟩ := GlobalTheory.T.trace_integral_of_small_at_other_places T.Q.c.F C.d.c₂.F p la hla m y
  refine ⟨N, fun b hb v hv => ?_⟩
  have hx : ∀ k, 0 ≤ v (β k) := fun k => hβi k v hv
  obtain ⟨⟨q, T0, io, e, ho, pt, hpt, eta, heta, rfl⟩, rfl⟩ := hv
  have hx' : ∀ k, valV T0.V (evI pt (β k)) ≤ 1 := fun k => (nval_nonneg_iff ho.1 _).1 (hx k)
  have hs : ∀ (s : Finset (Fin m)) (t : Fin m → T.Q.c.F),
      evI pt (∑ k ∈ s, t k • β k) = ∑ k ∈ s, io (t k) * evI pt (β k) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simpa using (isEval_evI pt).zero ()
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evI_add, evI_smul, ih]
  show 0 ≤ nval T0.V e (evI pt _)
  rw [nval_nonneg_iff ho.1, hs]
  exact hN b hb T0 hpt io e ho (fun k => evI pt (β k)) hx'
    (fun T' i e' τ e'' he' hi hT' hτ ho' =>
      GlobalTheory.T.baseSections_values_integral_at_coverLift D T hL j hj σ C hU la a n m β g (fun k => (hβ k).1) hgs hgp y hgi T0 io pt hpt T' i e' τ e'' he' hi hT' hτ ho')

end GlobalTheory.TraceIdem
end
end

section

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRefTup

section IdempotentCombination
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

theorem conj_sum_eq (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ}
    {b : Fin m → ℂ} {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {g : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (ha : Expands O κ Φ a f) (hb : Expands O κ Φ b g) (x : GA D (Wc D i)) :
    ∑ k, τ (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) x) =
    ∑ k, τ (b k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (g k : T.toCore.R ((i : ℕ) + 1)) x) := by
  have h0 : Expands O κ (fun _ => 0) (Fin.append a (fun k => -b k)) (Fin.append f g) := by
    intro y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← ha y, ← hb y, add_neg_cancel]
  have h1 := hZ.2 _ _ _ h0 x
  rw [Fin.sum_univ_add] at h1
  simp only [Fin.append_left, Fin.append_right, map_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at h1
  linear_combination (-1 : ℂ) * h1

theorem conjFun_lin (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ Φ' Ψ Ψ' : GA D (Wc D i) → ℂ}
    (h1 : ConjFun O κ τ 1 Φ Φ') (h2 : ConjFun O κ τ 1 Ψ Ψ') (c d : ℂ) :
    ConjFun O κ τ 1 (fun x => c * Φ x + d * Ψ x) (fun x => τ c * Φ' x + τ d * Ψ' x) := by
  obtain ⟨n, a, f, ha⟩ := h1.1
  obtain ⟨m, b, g, hb⟩ := h2.1
  have hs : Expands O κ (fun x => c * Φ x + d * Ψ x) (Fin.append (fun k => c * a k) (fun k => d * b k)) (Fin.append f g) := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ha x, hb x, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, hs⟩, fun N e h he x => ?_⟩
  simp only [one_mul]
  rw [conj_sum_eq O κ τ hZ he hs x, Fin.sum_univ_add, h1.2 _ _ _ ha x, h2.2 _ _ _ hb x]
  simp only [Fin.append_left, Fin.append_right, one_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem conjFun_sum (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) : ∀ (n : ℕ) (α : Fin n → ℂ)
    (Φ Φ' : Fin n → GA D (Wc D i) → ℂ), (∀ k, ConjFun O κ τ 1 (Φ k) (Φ' k)) →
    ConjFun O κ τ 1 (fun g => ∑ k, α k * Φ k g) (fun g => ∑ k, τ (α k) * Φ' k g) := by
  intro n
  induction n with
  | zero => intro α Φ Φ' _; simpa using hZ
  | succ n ih =>
    intro α Φ Φ' hk
    have h := conjFun_lin O κ τ hZ (hk 0) (ih (fun k => α k.succ) (fun k => Φ k.succ) (fun k => Φ' k.succ)
      (fun k => hk k.succ)) (α 0) 1
    simp only [map_one, one_mul] at h
    simpa only [Fin.sum_univ_succ] using h

end IdempotentCombination



theorem conjFun_base_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∀ y y' : (R.HV i A.μ0).H, ConjForm R i τ c A.μ0 A.μ0 y y' → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase c hc
  have h2 := GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hcore hfin hfw hQ i hpins
  obtain ⟨M, hMp, hMl, hMe, hMn, hMc, hMx, hMs⟩ := h2
  have h3 := GlobalTheory.T.exists_rootOfUnity_coverFunction_reference_tuple hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs
  have h4 := GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs h3.choose h3.choose_spec.1 h3.choose_spec.2
  refine ⟨h4.choose, h4.choose_spec.1, fun τ hB y y' hyy => ?_⟩
  have hP := h4.choose_spec.2
  let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  haveI := hMn
  let ta : M.c'.F ≃+* M.c'.F := (τa.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => AlgEquiv.restrictNormal_commutes τa M.c'.F a
  have hct : ConjTup R τ A.μ0 A.μ0 := by
    refine ⟨rfl, fun x => ?_⟩
    have h1 := hcore.lev.xi A.μ0
    rw [hcore.lev.xi_base] at h1
    rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x]
    simp
  have h5 := GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hcore hfw i T0 id M hMp τ ta hta hB c ((hMe c).1 hc) hMx A.μ0 A.μ0 hct y y' hyy
  obtain ⟨n, α, ys, ys', hy, hy', hk⟩ := h5
  have hZ : ConjFun (O i) (κ i) τ 1 (fun _ => 0) (fun _ => 0) := by
    have := hP τ ta hta hB 0 0 (fun h => ⟨0, 0, by simp, by rw [map_zero, map_zero]; rfl, by rw [map_zero, map_zero]; rfl⟩)
    simpa using this
  have hL := conjFun_sum (O i) (κ i) τ hZ n α
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys k) (v₀ i (sg0 D A)) g)
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys' k) (v₀ i (sg0 D A)) g) (fun k => hP τ ta hta hB (ys k) (ys' k) (hk k))
  subst hy hy'
  convert hL using 2 with g g

  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.ConjRefTup
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



set_option maxRecDepth 100000 in
theorem GlobalTheory.ConjTwist.conjFun_ser : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc u hu τ hfix
  obtain ⟨ζ0, hζ, H⟩ := GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion hCI D G Pl0 T0 A T R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc τ hfix
  refine ⟨ζ0, hζ, fun t t' ht => ?_⟩
  obtain ⟨s, Hs⟩ := H t t' ht
  refine ⟨s, fun h hh x x' hx => ?_⟩
  obtain ⟨y, y', hy, he⟩ := GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries D G Pl0 T0 A T R F κ v₀ hC hFW i Unit (fun _ => A.μ0) (O i) hP.2 c hc τ t t' hfix ht h hh x x' hx
  have hv : (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) := funext hu
  have e1 : (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) = fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).1, hv]
  have e2 : (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) = fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).2, hv]
  rw [e1, e2]
  exact Hs y y' hy
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  first | exact @GlobalTheory.ConjTwist.conjFun_ser | exact GlobalTheory.ConjTwist.conjFun_ser | (intros; apply GlobalTheory.ConjTwist.conjFun_ser <;> assumption)

end
end
