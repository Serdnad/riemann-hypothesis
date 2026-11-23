module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStandardIsometryFourthPowerSplitPrime
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KerT.Bar

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Box

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap _ _ _ _).2 (by simpa using hy))
    exact (mem_localization_gmap _ _ _ _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap _ _ _ _).1 hy)
    exact (mem_localization_gmap _ _ _ _).2 (by simpa using this)

theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    g'.symm.toLinearMap ∘ₗ (c • x) ∘ₗ g.toLinearMap = c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine LinearMap.ext fun y => ?_
  exact equiv_osmul g'.symm c (x (g y))

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K} (h : InBox S cA cB N N' Ξ)
    (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : (cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) ∈ homAt S N N' := h.1 _ hx
    change (cA : 𝓞 E) • x ∈ homAt S (gmap g N) (gmap g' N')
    rw [mem_homAt_gmap, conj_osmul]
    exact h1
  · rintro x _ ⟨z, hz, rfl⟩
    have h1 := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) = _
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]
    exact h1

end Box

variable {X : Fields}

theorem framed_gmap {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) (fun P : SB => g * fr P) := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem mem_valAt_gmap (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    y ∈ valAt w lam (gmap γ.1 L) ↔ ∃ z ∈ valAt w lam L, rhoVr X.emb lam (ufGL X.E n γ) z = y := by
  unfold valAt
  rw [delAtr_gmap, Formalism.BasicNotions.SkeletonIndexLemmas.localization_map₂]
  exact Iff.rfl

theorem rho_inv_apply {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem barTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet (E := Z.X.E) (n := Z.R.N i) (ST := Z.Pr.vT u) (SG := SG)) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet (E := Z.X.E) (n := Z.R.N (i + 1)) (ST := Z.Pr.vT u) (SG := SG')) (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y') → BarTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  obtain ⟨y', hy', he⟩ := hstd (((γ, 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG)) • d) (fun P => γ.1 * fr P)
    (((γ', 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG')) • d') (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))
    ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩ (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1)
    (inBox_gmap hbox γ.1 γ'.1) (fun x => hint _) (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by
      rw [DecoSet.smul_val, Deco.Lsh_act _ γ.2, mem_valAt_gmap]
      exact ⟨y, hy, rfl⟩)
  rw [DecoSet.smul_val, Deco.Lsh_act _ γ'.2, mem_valAt_gmap] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  refine ⟨z, hz, ?_⟩
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul] at he
  have h2 := congrArg (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ'⁻¹)) he
  rwa [rho_inv_apply, rho_inv_apply] at h2

end GlobalTheory.KerT.Bar
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerT.PAll

section Hom

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap P g N _).2 (by simpa using hy))
    exact (mem_localization_gmap P g' N' _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap P g N _).1 hy)
    refine (mem_localization_gmap P g' N' _).2 ?_
    simpa using this

omit [NumberField E] [StarRing E] in
theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    (g'.symm.toLinearMap ∘ₗ (c • x : HomE E a b) ∘ₗ g.toLinearMap : HomE E a b) =
      c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) := by
  rw [← algebraMap_smul E c x, ← algebraMap_smul E c, LinearMap.smul_comp, LinearMap.comp_smul]

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB N N' Ξ) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h1 : ((cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b)) ∈ homAt S N N' := h.1 _ hx
    change ((cA : 𝓞 E) • x) ∈ homAt S (gmap g N) (gmap g' N')
    rwa [mem_homAt_gmap, conj_osmul]
  · obtain ⟨z, hz, rfl⟩ := hy
    have := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    refine Eq.trans ?_ this
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) =
      Ξ (_ + (cB : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap : HomE E a b))
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]

end Hom

variable {X : Fields} {n : ℕ}

theorem framed_gmap {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) fun P => g * fr P := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem rho_inv_apply (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem mem_localization_map {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (f : V →ₗ[𝓞 K] V) (hf : Function.Injective f) (M : Submodule (𝓞 K) V) (y : V) :
    f y ∈ localization₂ w.asIdeal (M.map f) ↔ y ∈ localization₂ w.asIdeal M := by
  rw [mem_locP, mem_locP]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← map_smul]
  exact ⟨fun ⟨z, hz, h⟩ => hf h ▸ hz, fun h => ⟨_, h, rfl⟩⟩

theorem rho_mem_valAt (w : HeightOneSpectrum (𝓞 X.K)) (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ) y ∈ valAt w lam (gmap γ.1 L) ↔ y ∈ valAt w lam L := by
  unfold valAt
  rw [delAtr_gmap]
  exact mem_localization_map w ((rhoVr X.emb lam (ufGL X.E n γ)).restrictScalars (𝓞 X.K))
    (Function.LeftInverse.injective (rho_inv_apply lam γ)) _ y

theorem pTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet (E := Z.X.E) (n := Z.R.N i) (ST := Z.Pr.vT u) (SG := SG)) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet (E := Z.X.E) (n := Z.R.N (i + 1)) (ST := Z.Pr.vT u) (SG := SG')) (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L) → PTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  have e1 : (((γ, 1) : UF Z.X.E (Z.R.N i) × GLG (E := Z.X.E) (n := Z.R.N i) (SG := SG)) • d).1.Lsh = gmap γ.1 d.1.Lsh :=
    Deco.Lsh_act d.1 γ.2 1
  have e2 : (((γ', 1) : UF Z.X.E (Z.R.N (i + 1)) × GLG (E := Z.X.E) (n := Z.R.N (i + 1)) (SG := SG')) • d').1.L = gmap γ'.1 d'.1.L :=
    Deco.L_act d'.1 γ'.1 1
  have h := hstd _ (fun P => γ.1 * fr P) _ (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩
    (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1) (inBox_gmap hbox γ.1 γ'.1) (fun _ => hint _)
    (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by rw [e1, rho_mem_valAt]; exact hy)
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, e2, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul,
    rho_mem_valAt] at h
  exact h

end GlobalTheory.KerT.PAll
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
  GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.AdjMem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (v : Sp E a) (y : Sp E b) : hStd E a v (adj x y) = hStd E b (x v) y := by
  have : x v = LinearMap.toMatrix' x *ᵥ v := (LinearMap.toMatrix'_mulVec x v).symm
  rw [this]
  change star v ⬝ᵥ ((LinearMap.toMatrix' x)ᴴ *ᵥ y) = star (LinearMap.toMatrix' x *ᵥ v) ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem apply_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {Q : HeightOneSpectrum (𝓞 E)} (hA : localization₂ Q.asIdeal AA = localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ Q.asIdeal N) : x v ∈ localization₂ Q.asIdeal N' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x', hx', rfl⟩ := hz
    obtain ⟨s, hs, hsv⟩ := (mem_locP _ _ _).1 hv
    obtain ⟨t, ht, htr⟩ := (mem_locP _ _ _).1 (hA ▸ le_locP Q AA hr)
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 htr
    refine (mem_locP _ _ _).2 ⟨t * s, fun hm => (Q.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
    have h1 := N'.smul_mem c (hx' _ hsv)
    have e : (t * s) • (r • x') v = c • x' (s • v) := by
      rw [← algebraMap_smul E c, hc, ← algebraMap_smul E s v, map_smul, LinearMap.smul_apply, ← algebraMap_smul E (t * s),
        smul_smul, smul_smul, map_mul, Algebra.smul_def t r]
      congr 1
      ring
    rw [e]
    exact h1
  | zero => exact zero_mem _
  | add x x' _ _ h h' => exact add_mem h h'
  | smul c x _ h => exact Submodule.smul_mem _ c h

theorem adj_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hA : localization₂ (conjPrime₂ P).asIdeal AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {y : Sp E b} (hy : y ∈ localization₂ P.asIdeal N') : adj x y ∈ localization₂ P.asIdeal N := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = conjPrime₂ Q := ⟨conjPrime₂ P, (GlobalTheory.CharValCompare.conjP_conjP P).symm⟩
  rw [GlobalTheory.CharValCompare.conjP_conjP] at hA
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN'.1.fg hN'.2] at hy
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN.1.fg hN.2]
  intro v hv
  rw [hStd_adj]
  exact hy _ (apply_mem_locP hA hx hv)

theorem adj_per_mem : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (P : HeightOneSpectrum (𝓞 X.E)), IsSdLat N → IsSdLat N'' →
    localization₂ (conjPrime₂ P).asIdeal A.AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 X.E) X.E) →
    ∀ x ∈ per A N N'', ∀ y ∈ localization₂ P.asIdeal N'', adj x y ∈ localization₂ P.asIdeal N :=
  fun _ _ _ _ _ _ _ hN hN' hA _ hx _ hy => adj_mem_locP hN hN' hA hx hy

end GlobalTheory.AdjMem
end
end

section

open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [e.map_add]
    exact I.add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => ?_
      · rw [map_mul]
        exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
      · rw [e.symm.map_add]
        exact add_mem ha hb
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]


end Vp

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)



end Val

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

end Parts

end GlobalTheory.CharValCompare
end
end

section

noncomputable section

namespace GlobalTheory.ClsPLocBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem exists_isLocBasis_clsP : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP),
    ∃ B : GL (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B := by
  intro D u Ch chOf Tf w c
  have hL : Submodule.IsFullLattice D.host.E (Tf.clsP.lat c) :=
    Formalism.MainNotions.G.ChF.isLattice_of_hat Tf.clsP.lev.Lb (Tf.clsP.lat c) Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span
      (Tf.clsP.y c).1 (Tf.clsP.y_lat c)
  have hspan : Submodule.span D.host.E (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) = ⊤ := by
    have hG := Formalism.UG.P.csGlob_lattice (F := D.host.F) Tf.clsP.lev.Lb Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span (Tf.clsP.y c).1
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := D.host.F) _ x ((Tf.clsP.y_lat c _).2 hx)
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (D.what₂.places.resChar w) D.host.E (Tf.clsP.lat c) hL.fg hspan

end GlobalTheory.ClsPLocBasis
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.exists_standard_isometry_fourthPower_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), Formalism.L2.Th1.H.StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g ∧ ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) ∧ ‖ι e‖ = 1 ∧ Formalism.L2.Th1.H.tens4 B.thMM = e • Formalism.L2.Th1.H.kernel4 B.L B.ω₀ B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  first | exact @GlobalTheory.CmThetaMoment.isomStd | exact GlobalTheory.CmThetaMoment.isomStd | (intros; apply GlobalTheory.CmThetaMoment.isomStd <;> assumption)
end
