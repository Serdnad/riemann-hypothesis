module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle528
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle177
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Unramified.LocalStructure
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.GaloisValuations.GlobalB
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)


open MonObj in
theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Ext

end GlobalTheory.HTFrame
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem latDR_subset_latHT :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X), latDR t x ⊆ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x v hv
  obtain ⟨xO, hx, vO, htan, hvO⟩ := hv
  have h1 : epsMul (1 : C) = RingHom.id (DualNumber C) := by
    ext a <;> simp [epsMul]
  have h2 : spMap (RingHom.id (DualNumber C)) = 𝟙 _ := by
    simp [spMap]
  refine ⟨xO, hx, 0, vO, htan, ?_, ?_⟩
  · rw [pow_zero, h1, h2, Category.id_comp, hvO]
  · intro n c g _
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top

end GlobalTheory.ShFam.Pad
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

abbrev PtFn (Y : Var F) : Type := ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

def IsIndep {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def minor {R : Type} [CommRing R] {m g k : ℕ} (a : Fin m → Fin g → R) (hk : k ≤ m) (s : Fin k → Fin g) : R :=
  (Matrix.of fun l i => a (Fin.castLE hk l) (s i)).det

def DlogIs {O : Type} [CommRing O] {x : Sp O ⟶ X} (p n : ℕ) (c : TorsChar t x (p ^ n)) {g : ℕ}
    (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)) (h : Fin g → O) : Prop :=
  ∀ (a : Fin g → O) (v : Sp (DualNumber O) ⟶ t.G.left), IsCombAtG t x e a v →
    ∀ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ v →
        (c.χ _ w : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (∑ i, h i * a i)

def Thru {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (u : Sp B ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : R →+* S) (w : Sp S ⟶ t.G.left) : Prop :=
  ∃ β : B →+* S, β.comp (algebraMap R B) = φ ∧ spMap β ≫ u = w

structure IsFinPart {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) : Prop where
  finite : Module.Finite R B
  free : Module.Free R B
  tors : u ^ q = 1
  mono : ∀ (S : Type) [CommRing S] (β β' : B →+* S), β.comp (algebraMap R B) = β'.comp (algebraMap R B) →
    spMap β ≫ u.left = spMap β' ≫ u.left → β = β'
  isOpen : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Over.mk (spMap φ ≫ x) ⟶ t.G), w ^ q = 1 →
    (∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Thru t u.left ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left)) → Thru t u.left φ w.left
  one : ∀ (S : Type) [CommRing S] (φ : R →+* S), Thru t u.left φ (1 : Over.mk (spMap φ ≫ x) ⟶ t.G).left
  mul : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G),
    Thru t u.left φ w.left → Thru t u.left φ w'.left → Thru t u.left φ (w * w').left
  sect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[R] R, β = (β.comp (algebraMap R B)).comp σ.toRingHom
  inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Tangent

end GlobalTheory.LineNorm
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PtComp

theorem disjoint_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hsm : Smooth f)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  refine CompSplitPfD.cspD_disj (fun x => ?_) Z Z' hZ hZ' hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have h1 := HasRingHomProperty.appLE (P := @Smooth) f hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp)
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V (fun p _ => by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) K) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem connectedComponent_mem {X : Type} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite)
    (hd : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, Z ≠ Z' → Disjoint Z Z') (z : X) :
    connectedComponent z ∈ irreducibleComponents X ∧ IsOpen (connectedComponent z) := by
  have hV := irreducibleComponent_mem_irreducibleComponents z
  have hU : irreducibleComponent z = (⋃ W ∈ irreducibleComponents X \ {irreducibleComponent z}, W)ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hp W hW hpW
      exact Set.disjoint_left.1 (hd _ hW.1 _ hV hW.2) hpW hp
    · intro hp
      by_contra hpZ
      exact hp _ ⟨irreducibleComponent_mem_irreducibleComponents p,
        fun h => hpZ ((show irreducibleComponent p = _ from h) ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  have ho : IsOpen (irreducibleComponent z) := by
    rw [hU]
    exact ((hfin.subset Set.diff_subset).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents _ hW.1).isOpen_compl
  have e : connectedComponent z = irreducibleComponent z :=
    ((IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, ho⟩ mem_irreducibleComponent)).antisymm
      irreducibleComponent_subset_connectedComponent
  rw [e]
  exact ⟨hV, ho⟩

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem preimage_connectedComponent_mem (Z : Model Xo c β) (hsm : Smooth (genStr Z)) (z : gen Z) :
    Z.jQ ⁻¹' connectedComponent z ∈ irreducibleComponents (Xo.XF c) := by
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  obtain ⟨h1, h2⟩ := connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => disjoint_of_smooth (genStr Z) hsm W W' hW hW') z
  have := Z.jQ_open
  exact preimage_mem_irreducibleComponents h1 Z.jQ.isOpenEmbedding
    (Z.jQ_dense.inter_open_nonempty _ h2 ⟨z, mem_connectedComponent⟩)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_equiv : ∃ q : s.Comp ≃ Comp (S.Xo κ.l) κ.c, ∀ k z,
    OnComp s k z ↔ (q k).1 = s.T.Z.jQ ⁻¹' connectedComponent z := by
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  have hne : ∀ k, ((s.U κ.σ₀).X k).dom.Nonempty := fun k => GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp _ _ _ _ _ _ κ.σ₀ N (s.U κ.σ₀) hσ (s.unf _ hσ).1 hne s.geo
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q, fun k z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨x, hx⟩
    by_contra hn
    let pt : Sp (CAt κ.σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
      ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩ fun e => hn (congrArg Subtype.val e)) (hq k x pt) (hx pt)
  · obtain ⟨x, hx⟩ := hne k
    refine ⟨⟨x, hx⟩, fun pt => ?_⟩
    have := hq k ⟨x, hx⟩ pt
    rw [h] at this
    exact this

theorem existsUnique_onComp (z : gen s.T.Z) : ∃! k, OnComp s k z := by
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q.symm ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩, (hq _ _).2 (by rw [Equiv.apply_symm_apply]),
    fun k hk => ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext ((hq _ _).1 hk)

theorem onComp_compPt (y : Pt s) (pt : Sp Qb) : OnComp s (compPt s y) (y.y pt) := by
  obtain ⟨k, hk, -⟩ := existsUnique_onComp s (y.y pt)
  have : ∃ k, ∀ pt', OnComp s k (y.y pt') :=
    ⟨k, fun pt' => (Subsingleton.elim (α := PrimeSpectrum Qb) pt pt') ▸ hk⟩
  exact Classical.epsilon_spec this pt

end GlobalTheory.ShFam.PtComp
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open Pointwise

namespace GlobalTheory.WittFracPlace

theorem valuation_intCast_lt_one_iff {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime)
    (h : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx
  constructor
  · intro hn
    by_contra hd
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd
    have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have := Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul, mul_comm, Int.cast_natCast]
    exact hmul m _ h

theorem exists_smul_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    (A A' : ValuationSubring Ω) (h : A.valuation (p : Ω) < 1) (h' : A'.valuation (p : Ω) < 1) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, g • A = A' := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by
      have h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom := by
        rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
      rw [hb, Ideal.mem_bot] at h1
      exact hp.ne_zero (by exact_mod_cast h1)⟩
  have key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 →
      ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal := by
    intro B hB x
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n
    have e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω) :=
      map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n
    rw [e, e2, valuation_intCast_lt_one_iff B hp hB]
    change _ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]
  exact ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')

theorem valuation_lt_one_of_inv_notMem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (h : x⁻¹ ∉ A) :
    A.valuation x < 1 := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le] at h
  have h0 : A.valuation x ≠ 0 := fun e => by simp [e] at h
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h

theorem exists_emb_inducing (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : (p : 𝓞 L) ∈ v.asIdeal) (V : ValuationSubring ℂ) (hV : (p : ℂ)⁻¹ ∉ V) :
    ∃ e : L →+* ℂ, ∀ x, e x ∈ V ↔ v.valuation L x ≤ 1 := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ L Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let ι : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨A', hA'⟩ := GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)
  have hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1 := fun x => by
    rw [← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]
  have h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    rwa [ValuationSubring.mem_comap, map_inv₀, map_natCast])
  have h2 : A'.valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    have h3 : v.valuation L (p : L) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv
      rw [← map_natCast (algebraMap (𝓞 L) L) p]
      exact this
    have h4 : v.valuation L (p : L) ≠ 0 := by simpa using hp.ne_zero
    rw [← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)
  obtain ⟨g, hg⟩ := exists_smul_eq hp _ _ h1 h2
  refine ⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩
  rw [← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_jcPin : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p), ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc := by
  intro D p hp la
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex p
  obtain ⟨V, -, -, -, hV⟩ :=
    GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j
  have hp' : (p : ℂ)⁻¹ ∉ V := by
    rw [← map_natCast j, ← map_inv₀, hV]
    rintro ⟨a, ha⟩
    have hinj := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)
    have h0 : (p : DV.KW p) ≠ 0 := fun e => hp.out.ne_zero (by
      have := congrArg j e
      rw [map_natCast, map_zero] at this
      exact_mod_cast this)
    refine (WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit
      (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]
  obtain ⟨e, he⟩ := exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'
  have : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL
  refine ⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩
  · rw [← he, ← hτ, ValuationSubring.mem_comap]
    simp
  · rw [← hV, ValuationSubring.mem_comap]
    simp

end GlobalTheory.WittFracPlace
end
