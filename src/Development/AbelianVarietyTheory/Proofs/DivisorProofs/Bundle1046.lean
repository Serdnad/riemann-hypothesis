module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DivStart

theorem exists_locus_over_dense_open : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  intro R _ _ _ _ A _ hA V hV hsurj
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  let s₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨x₀, hx₀, -⟩ := hsurj s₀
  obtain ⟨W₀, hVW, hufd, c₀, hc₀⟩ := GlobalTheory.FactorialLocus.exists_isLocus A.left V hV ⟨x₀, hx₀⟩
  have hfib : ∀ x, A.hom x = s₀ → x ∈ W₀ := fun x hx =>
    hufd x (GlobalTheory.GenericFibreFactorial.ufd_stalk_of_generic R A.left A.hom x (by rw [hx]))
  obtain ⟨U, -, hsU, hUW⟩ := GlobalTheory.Tube.exists_affine_preimage_le A.left (Sp R) A.hom s₀ W₀ hfib
  have hle : A.hom ⁻¹ᵁ U ⊔ V ≤ W₀ := sup_le hUW hVW
  refine ⟨U, GlobalTheory.CechPic.pull (A.left.homOfLE hle) c₀, ⟨s₀, hsU⟩, ?_⟩
  have h := GlobalTheory.LocusPull.isLocus_pull (A.left.homOfLE hle) hc₀
  convert h using 1
  ext x
  change (A.hom ⁻¹ᵁ U ⊔ V).ι x ∈ V ↔ W₀.ι (A.left.homOfLE hle x) ∈ V
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

end GlobalTheory.DivStart
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem extend_isLocus_of_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  intro X _ _ hX V W hV hVW hW c hloc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨r, hr⟩ := IsLocus.exists_sec (pull_isLB hL W.ι) hloc
  obtain ⟨t, ht, -⟩ := ((GlobalTheory.extension_over_codim_two X hX).1 W hW).2.1 L r
  have e : GlobalTheory.secPull t W.ι = r := (GlobalTheory.lbSec_ext fun i => rfl).trans ht
  have h1 : W.ι ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t = W.ι ⁻¹ᵁ V := by
    rw [← GlobalTheory.nonzeroLocus_secPull, e, hr]
  have key : ∀ x (hx : x ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t ↔ x ∈ V := fun x hx => by
    have := congrArg (fun U : W.toScheme.Opens => (⟨x, hx⟩ : W.toScheme) ∈ U) h1
    exact Iff.of_eq this
  refine ⟨L, hL, t, rfl, ?_⟩
  exact GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' X hX V (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) hV (fun x hx => (key x (hVW hx)).2 hx)
    (fun z hz hz1 => (key z (hW z hz1)).1 hz)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus : (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) := by
  first | exact @GlobalTheory.LocusPull.locus_pull | exact GlobalTheory.LocusPull.locus_pull | (intros; apply GlobalTheory.LocusPull.locus_pull <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem isLattice_of_eq_span_frac_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) (M N : Submodule (𝓞 K) V)
    (h : M = Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ N, x = (a : K) • y})
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K N := by
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ (0 : K) := by
    by_contra hc
    push_neg at hc
    exact hI (FractionalIdeal.eq_zero_iff.2 hc)
  refine ⟨?_, ?_⟩
  · let f : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V a).restrictScalars (𝓞 K)
    have hf : Function.Injective f := fun x y hxy => smul_right_injective V ha0 hxy
    have hle : N.map f ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      rw [h]
      exact Submodule.subset_span ⟨a, haI, y, hy, rfl⟩
    have hfg : (N.map f).FG := Submodule.FG.of_le hM.fg hle
    exact Submodule.fg_of_fg_map_injective f hf hfg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isLattice_comap_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (e : W ≃ₗ[K] V) (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.comap ((e : W →ₗ[K] V).restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective ((e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.injective ?_
    rw [Submodule.map_comap_eq_of_surjective
      (f := (e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.surjective]
    exact hN.fg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem nuLat_comap_isLattice : ∀ (D : D7) (L : SizeData₂ D), Formalism.BasicNotions.DV.NprimeDef D L → ∀ u, Submodule.IsLattice D.what₂.LL (D.div.Nu u).L → ∀ (d : ℕ) (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Submodule.IsLattice D.what₂.LL ((L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D L hdef u hL d e
  have hI : Formalism.BasicNotions.DV.Iu D L u ≠ 0 := by
    unfold Formalism.BasicNotions.DV.Iu
    rw [Finset.prod_ne_zero_iff]
    intro w _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)
  exact isLattice_comap_equiv e _
    (isLattice_of_eq_span_frac_smul (Formalism.BasicNotions.DV.Iu D L u) hI _ _ (hdef u) hL)

end GlobalTheory.ColRows
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.coverUpq_closure_exp_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q, Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  first | exact @GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | exact GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | (intros; apply GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan <;> assumption)
end

section

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)


open Classical in
def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNormsUnit

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem exists_prime {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {Sg : Set ℕ} (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
  classical
  have hg : ∀ i, P ∈ Pr.vG i → ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
    intro i hi
    refine ⟨Pr.g i, hPr.g_prime i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ (mem_of_divs hi), fun hd => ?_⟩
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)
  unfold Sall at hP
  simp only [rowSG, uSG, qe_one, Primes.vGs, Finset.mem_union, Finset.notMem_empty, or_false] at hP
  rcases hP with h | h | h
  · have h0 : Pr.piT u ∈ P.asIdeal := mem_of_divs h
    have hT : (Pr.T u : 𝓞 X.E) ∈ P.asIdeal := hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ h0
    refine ⟨Pr.T u, hPr.T_prime u, hT, fun hd => ?_⟩
    have h1 : (Pr.T u : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hT
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory.ColNormsUnit
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SemilocalClasses

theorem card_finset_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) (s : Finset Q) : s.card ≤ n ^ Module.finrank ℚ V := by
  classical
  obtain ⟨σ, hσ⟩ := hπ.hasRightInverse
  let F : Submodule ℤ A := Submodule.span ℤ (↑(s.image σ) : Set A)
  haveI : Module.Finite ℤ F := Module.Finite.span_of_finite ℤ (Finset.finite_toSet _)
  let g : F →ₗ[ℤ] V := f.toIntLinearMap ∘ₗ F.subtype
  have hg : Function.Injective g := hf.comp F.subtype_injective
  haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  haveI : Module.IsTorsionFree ℤ F := Function.Injective.moduleIsTorsionFree g hg (by simp)
  haveI : Module.Free ℤ F := Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank ℤ F ≤ Module.finrank ℚ V := by
    let b := Module.finBasis ℤ F
    have h1 : LinearIndependent ℤ (g ∘ b) := b.linearIndependent.map' g (LinearMap.ker_eq_bot.2 hg)
    have h2 : LinearIndependent ℚ (g ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
    simpa using h2.fintype_card_le_finrank
  let p : F →+ Q := π.comp F.subtype.toAddMonoidHom
  have hle : (nsmulAddMonoidHom (α := F) n).range ≤ p.ker := by
    rintro _ ⟨x, rfl⟩
    simpa [p] using h0 x
  have hidx : (nsmulAddMonoidHom (α := F) n).range.index = n ^ Module.finrank ℤ F :=
    AddSubgroup.index_range_nsmul F n
  have hpos : 0 < n ^ Module.finrank ℤ F := pow_pos hn _
  have hdvd : p.ker.index ∣ n ^ Module.finrank ℤ F := hidx ▸ AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_ker] at hdvd
  have hne : Nat.card p.range ≠ 0 := fun h => by
    rw [h] at hdvd; exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  haveI : Finite p.range := Nat.finite_of_card_ne_zero hne
  have hsub : (↑s : Set Q) ⊆ (p.range : Set Q) := fun q hq =>
    ⟨⟨σ q, Submodule.subset_span (by simpa using ⟨q, hq, rfl⟩)⟩, hσ q⟩
  calc s.card = Nat.card (↑s : Set Q) := by simp
    _ ≤ Nat.card p.range := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ n ^ Module.finrank ℤ F := Nat.le_of_dvd hpos hdvd
    _ ≤ n ^ Module.finrank ℚ V := Nat.pow_le_pow_right hn hr

theorem finite_card_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) : Finite Q ∧ Nat.card Q ≤ n ^ Module.finrank ℚ V := by
  have h := card_finset_le f hf π hπ n hn h0
  have hfin : Finite Q := by
    by_contra hinf
    haveI : Infinite Q := not_finite_iff_infinite.1 hinf
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Q (n ^ Module.finrank ℚ V + 1)
    have := h s
    omega
  refine ⟨hfin, ?_⟩
  haveI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card]
  exact h Finset.univ

theorem finite_card_classes : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ a b S L L' cA c _ _ hA hc
  haveI : Module.Finite ℚ (HomE E a b) := Module.Finite.trans E (HomE E a b)
  have hd : Module.finrank ℚ (HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E (HomE E a b), Module.finrank_linearMap]
    simp [mul_assoc]
  rw [← hd]
  refine finite_card_le (divLat cA (homAt S L L')).subtype.toAddMonoidHom (Submodule.subtype_injective _)
    ((mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (cA * c) (Nat.mul_pos hA hc) fun x => ?_
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(cA : 𝓞 E) • (x : HomE E a b), x.2, ?_⟩
  show (c : 𝓞 E) • (cA : 𝓞 E) • (x : HomE E a b) = (cA * c) • (x : HomE E a b)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, mul_nsmul]

end GlobalTheory.SemilocalClasses
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem liftFr_lifts : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (w : SG), (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x :=
  fun _ _ _ _ _ _ _ d w => GlobalTheory.TopStep.liftFr_spec d.2 w

end GlobalTheory.ColNorms
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbers

theorem card_orbits_le_principal {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {G' D' : Type} [Group G'] [MulAction G' D']
    (p : D' → DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (hp : Function.Injective p)
    (h : ∀ (g : UF E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG (E := E) (n := n) (SG := SG))) • p x)
    [Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)))] :
    Nat.card (MulAction.orbitRel.Quotient G' D') ≤
      Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG))) := by
  refine Nat.card_le_card_of_injective
    (fun c : MulAction.orbitRel.Quotient G' D' =>
      (Quotient.mk (MulAction.orbitRel _ _) (p (Quotient.out c)) :
        MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG (E := E) (n := n) (SG := SG)))) (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)))) ?_
  intro c c' hcc
  obtain ⟨⟨⟨g, k⟩, hgk⟩, hg⟩ := Quotient.exact hcc
  have hk : k = 1 := (Subgroup.mem_prod.1 hgk).2
  subst hk
  obtain ⟨g', hg'⟩ := h g (Quotient.out c')
  have he : g' • Quotient.out c' = Quotient.out c := hp (hg'.trans hg)
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound ⟨g', he⟩

end GlobalTheory.ChainClassNumbers
end
end

section

open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  first | exact @GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | exact GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | (intros; apply GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem GlobalTheory.ColNorms.jetC_sum_mul : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  intro ι _ a b cD α R c F hF m
  have key : ∀ (k : ℕ) (v : Fin k → VCx ι a b),
      iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v =
        ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v := by
    intro k v
    have hC : ∀ i ∈ R, ContDiff ℂ k (F i) := fun i hi =>
      GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _
    have h1 := iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k)
      (fun i hi => contDiff_const.mul (hC i hi))
    rw [h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 := iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0)
      (hC i hi).contDiffAt
    simp only [smul_eq_mul] at h2
    rw [h2]
    simp
  unfold jetC derivAt0
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end
