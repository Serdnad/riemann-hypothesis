module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyReductionModuloHighDegree
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle262
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  apply GlobalTheory.BadCount.Inh.isUniUp_mul <;> assumption

end GlobalTheory.UnipotentUpperMul
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AtQDTypes

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  apply GlobalTheory.HubFon.g_ne_q_d <;> assumption

theorem l_not_mem_gset {D : D7} (i : D.nd.Loc) (h : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) :
    D.nd.l i ∉ TwistedPlaces.gset D := by
  unfold TwistedPlaces.gset
  intro hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases h with h | h
  · exact (g_ne_q_d D 0).1 (hm ▸ h)
  · exact (g_ne_q_d D 0).2 (hm ▸ h)
  · exact (g_ne_q_d D 1).1 (hm ▸ h)
  · exact (g_ne_q_d D 1).2 (hm ▸ h)

end GlobalTheory.AtQDTypes
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  apply GlobalTheory.Cyc.exists_basis_of_fullLattice <;> assumption

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)


include hφ in
omit [IsDomain R] in
theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]


include hφ hint in
theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3


include hφ hint in
theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TypePlacesExhaust

variable {R : Ranks} (H : Host R)

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap ((cInt H).symm : 𝓞 H.E →+* 𝓞 H.E) (cInt H).symm.surjective w

variable {H}

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (y : 𝓞 H.E) :
    y ∈ (conjPl H w).asIdeal ↔ (cInt H).symm y ∈ w.asIdeal := Iff.rfl

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hy
  have e : y = cInt H x := RingOfIntegers.ext (by rw [hy]; rfl)
  subst e
  rw [mem_conjPl, RingEquiv.symm_apply_apply]

theorem conjPl_injective : Function.Injective (conjPl H) := by
  intro w w' h
  apply HeightOneSpectrum.ext
  ext x
  have := congrArg (fun u : HeightOneSpectrum (𝓞 H.E) => cInt H x ∈ u.asIdeal) h
  simp only [mem_conjPl, RingEquiv.symm_apply_apply] at this
  exact Iff.of_eq this

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show ((p : ℕ) : 𝓞 H.E) ∈ (conjPl H w).asIdeal
  rw [mem_conjPl, map_natCast]
  exact hw

theorem finrank_E (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem eq_plGw_or_isConjPl : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  apply GlobalTheory.TypePlaceCover.place_cover <;> assumption

end GlobalTheory.TypePlacesExhaust
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut

namespace GlobalTheory.UnrNoChi

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem chi_one_eq_one (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ)
    {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨-, e, he⟩ := hρ
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  simp only [hγ, Units.val_one, Matrix.map_one (toK D.nd i) (map_zero _) (map_one _), Matrix.one_mulVec, hu,
    LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

end GlobalTheory.UnrNoChi
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.Proof.QuotientLengthInfimum

open GlobalTheory.IndefiniteRowSideFullHecke

theorem length_quot_eq_iInf {O : Type} [CommRing O] [IsPrincipalIdealRing O] (I : Ideal O) :
    Module.length O (O ⧸ I) = ⨅ x ∈ I, Module.length O (O ⧸ Ideal.span {x}) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hx
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Ideal.span_singleton_generator I
    refine iInf₂_le_of_le (Submodule.IsPrincipal.generator I)
      (Submodule.IsPrincipal.generator_mem I) ?_
    rw [hg]

theorem mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) (y : O) :
    y ∈ ccAt T Z π ↔ ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = y := by
  have hs : Function.Surjective ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) :=
    fun a => ⟨algebraMap O T a, by simp⟩
  unfold ccAt
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  rfl

theorem div_le_iff_lengths (e c s h v q : ℕ∞) (he0 : e ≠ 0) (he : e ≠ ⊤) :
    ((c : ℝ≥0∞) / (e : ℝ≥0∞) ≤ (s : ℝ≥0∞) / (e : ℝ≥0∞) + (h : ℝ≥0∞) + (v : ℝ≥0∞) + (q : ℝ≥0∞) / (e : ℝ≥0∞)) ↔
      c ≤ s + e * h + e * v + q := by
  have he0' : (e : ℝ≥0∞) ≠ 0 := by simpa using he0
  have he' : (e : ℝ≥0∞) ≠ ⊤ := by simpa using he
  rw [← ENat.toENNReal_le, ← ENNReal.mul_le_mul_iff_right he0' he']
  simp only [mul_add, ENNReal.mul_div_cancel he0' he', ENat.toENNReal_add, ENat.toENNReal_mul]

theorem toENNReal_sum {ι : Type} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ a ∈ s, f a : ℕ∞) : ℝ≥0∞) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ENat.toENNRealRingHom f s

section Hyp

end Hyp

section Terms

variable (D : D7) (i : D.nd.Loc)

theorem ramLen_ne : SelmerSumLargePrime.ramLen D i ≠ 0 ∧ SelmerSumLargePrime.ramLen D i ≠ ⊤ := by
  have h := BaseSizes.vO_l D i
  unfold BaseSizes.vO BaseSizes.nlen at h
  change ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) / ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) = 1 at h
  constructor
  · intro h0; rw [h0] at h; simp at h
  · intro h0; rw [h0] at h; simp at h

theorem vCC_eq (π : D.nd.X i) :
    BaseSizes.vCC D i π = (SelmerSumLargePrime.ccLen D i π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.vCC BaseSizes.vO BaseSizes.nlen SelmerSumLargePrime.ccLen
  change ⨅ f ∈ D.nd.cc i, _ / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) = _
  apply le_antisymm
  · set I := ccAt (D.nd.T i) (D.nd.Z i) π with hI
    have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
    obtain ⟨f, hf, hfx⟩ := (mem_ccAt _ _ π _).1 (Submodule.IsPrincipal.generator_mem I)
    refine iInf₂_le_of_le f hf ?_
    rw [hfx, hg]
  · refine le_iInf₂ fun f hf => ?_
    refine ENNReal.div_le_div_right ?_ _
    rw [ENat.toENNReal_le, length_quot_eq_iInf]
    exact iInf₂_le _ ((mem_ccAt _ _ π _).2 ⟨f, hf, rfl⟩)

theorem sPi_eq (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    BaseSizes.sPi D i π ρ = (SelmerSumLargePrime.selLen D i ρ π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := rfl

theorem shaSum_eq : BaseSizes.shaSum D i = (SelmerSumLargePrime.shaSum D i : ℝ≥0∞) := by
  unfold BaseSizes.shaSum SelmerSumLargePrime.shaSum
  rw [toENNReal_sum]

theorem vClass_eq :
    BaseSizes.vClass D i = (((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) : ℝ≥0∞) := by
  unfold BaseSizes.vClass hE
  simp

theorem zetaP_eq (P : HeightOneSpectrum (𝓞 D.host.E)) : BaseSizes.zetaP D i P = SelmerSumLargePrime.zetaP D i P := rfl

theorem epsQ_eq : BaseSizes.epsQ D i = (SelmerSumLargePrime.twistLen D i : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.epsQ SelmerSumLargePrime.twistLen BaseSizes.vO BaseSizes.nlen
  rw [ENat.toENNReal_mul, toENNReal_sum, mul_div_assoc, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  rfl

theorem conclusion_iff (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    (BaseSizes.vCC D i π ≤ BaseSizes.sPi D i π ρ + BaseSizes.shaSum D i + BaseSizes.vClass D i + BaseSizes.epsQ D i) ↔
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i := by
  rw [vCC_eq, sPi_eq, shaSum_eq, vClass_eq, epsQ_eq]
  exact div_le_iff_lengths _ _ _ _ _ _ (ramLen_ne D i).1 (ramLen_ne D i).2

end Terms

end GlobalTheory.Proof.QuotientLengthInfimum

end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Integral D := by
  first | exact @GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral | exact GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral | (intros; apply GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.monodromy_reduction_modulo_high_degree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a := by
  first | exact @GlobalTheory.NModHigh.reduction | exact GlobalTheory.NModHigh.reduction | (intros; apply GlobalTheory.NModHigh.reduction <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain : ∀ {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → e * e = e → e * X₀ = X₀ → X₀ * e = X₀ → Set.InjOn ρ (Finset.Icc 1 t : Set ℕ) → ∏ c ∈ Finset.Icc 1 t, (Polynomial.X - Polynomial.C (ρ c)) = blockPol e X₀ → ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧ ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  first | exact @GlobalTheory.RootFactor.rank_one_and_sq | exact GlobalTheory.RootFactor.rank_one_and_sq | (intros; apply GlobalTheory.RootFactor.rank_one_and_sq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem finiteDimensional_Dst_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  by_cases hV : 0 < finrank ℚ_[l] V
  · have hK : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
    have hpos : 0 < finrank ℚ_[l] ↥(Dst P ρ) := by
      unfold IsSst at h
      rw [h]
      exact Nat.mul_pos hK hV
    exact Module.finite_of_finrank_pos hpos
  · have h0 : finrank ℚ_[l] V = 0 := Nat.eq_zero_of_not_pos hV
    haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (V ⊗[ℚ_[l]] Bst P) := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : V ⊗[ℚ_[l]] Bst P, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [hx x, hx y]
    infer_instance

end GlobalTheory.Pst
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiV_crisIncl_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  intro l _ P K V _ _ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [crisIncl_tmul, phiV_tmul, phiSt_C, φVB, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, P.PD_φ K b]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.PMon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monV_eq_zero_iff_exists_crisIncl : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 ↔ ∃ w, crisIncl P ℚ_[l] V w = z :=
  fun _ _ P V _ _ z => monV_eq_zero_iff_mem_range_crisIncl P _ V z

end GlobalTheory.PMon
end
