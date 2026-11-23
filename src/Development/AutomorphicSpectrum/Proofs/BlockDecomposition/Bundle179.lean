module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle167
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle168
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle134
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateSequenceTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle170
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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_singleton_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d), ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧ IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_empty_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d), ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.kaehler_free_cone_ring : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)), Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

def topEquiv : (⊤ : AddSubmonoid (Gam n d)) ≃ Gam n d := Equiv.Set.univ _

def lrBasis : Module.Basis (Gam n d) K (Lr K n d) :=
  (Module.Basis.ofRepr (AddMonoidAlgebra.coeffLinearEquiv K)).reindex topEquiv

theorem lrBasis_apply (g : Gam n d) : lrBasis (K := K) g = monL K g := by
  rw [lrBasis, Module.Basis.reindex_apply, Module.Basis.coe_ofRepr]
  rfl

def setEquiv (a : ℕ) : {D : Finset (E n d) // D.card = a} ≃ Set.powersetCard (Fin (n + d)) a where
  toFun D := ⟨D.1.map finSumFinEquiv.toEmbedding, by simpa using D.2⟩
  invFun s := ⟨s.1.map finSumFinEquiv.symm.toEmbedding, by simp⟩
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

theorem wedge_basis (bΩ : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K]) (h : ∀ e, bΩ e = dl e) (a : ℕ) :
    ∃ c : Module.Basis {D : Finset (E n d) // D.card = a} (Lr K n d) (Om K (Lr K n d) a),
      ∀ D, c D = wedge (K := K) (enumD D) := by
  refine ⟨((bΩ.reindex finSumFinEquiv).exteriorPower a).reindex (setEquiv a).symm, fun D => ?_⟩
  rw [Module.Basis.reindex_apply, exteriorPower.basis_apply]
  simp only [Equiv.symm_symm]
  unfold exteriorPower.ιMulti_family wedge
  congr 1
  funext i
  simp [Module.Basis.reindex_apply, h, enumD, setEquiv, Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem monW_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  intro K _ n d a
  obtain ⟨bΩ, h⟩ := GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis.exists_basis_dl (K := K) (n := n) (d := d)
  obtain ⟨c, hc⟩ := wedge_basis bΩ h a
  refine ⟨lrBasis.smulTower c, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, lrBasis_apply, hc]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
end
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.monomial_form_in_relative_image : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 → Tset g D.1 ⊆ S → ∃ ω ∈ relOm K (I0 n K S) a, omMap (incl le_top) a ω = monW K g D := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.relative_forms_map_mem_span : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (ω : Om K (R0 K n d S) a), ω ∈ relOm K (I0 n K S) a → omMap (incl le_top) a ω ∈ Submodule.span K {w : Om K (Lr K n d) a | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.exists_hermitian_congr_to_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det → ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | exact GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_congr_one <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem tsum_unitVec_eq {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (h : F → ℝ) :
    ∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, h (x.1 ()) =
      ∑' x : F, (IntOut T).indicator h x := by
  let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ (IntOut T) :=
    (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
      constructor
      · intro hx v hv
        exact hx v hv ()
      · intro hx v hv i
        exact hx v hv)
  rw [← tsum_subtype (IntOut T) h]
  exact e.tsum_eq (fun y : IntOut T => h y.1)

theorem tsum_eq_zero_add_of_finset {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' x : F, h x = h 0 + ∑' β : {β : F // β ≠ 0}, h β.1 := by
  rw [tsum_ne_zero_eq_sum h B hB hh, tsum_eq_sum (s := insert 0 B) ?_, Finset.sum_insert (fun h0 => hB 0 h0 rfl)]
  intro x hx
  simp only [Finset.mem_insert, not_or] at hx
  exact hh x hx.1 hx.2

theorem integral_unitVec_eq {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → ℝ) :
    ∫ y, f (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ y, f y ∂μ :=
  (measurePreserving_funUnique μ Unit).integral_comp' (g := f)

theorem tendsto_truncSum : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam T G ψ hG hGc hψ
  have hlocI : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : LocallyCompactSpace (Ainf F) := hlocI.2.1
  have : SecondCountableTopology (Ainf F) := hlocI.2.2.1
  have := hli.1
  have : SigmaFinite li := inferInstance
  have hsf : ∀ v, SigmaFinite (lam v) := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    have : LocallyCompactSpace (Fv F v) := hloc.2.1
    have : SecondCountableTopology (Fv F v) := hloc.2.2.1
    have := (hlam v).1
    infer_instance
  have key := hE F hF θ hθ li lam hli hlam Unit T (fun y => G (y ())) (fun v y => ψ v (y ()))
    (hG.comp (continuous_apply ())) (hGc.comp_homeomorph (Homeomorph.funUnique Unit (Ainf F)))
    (fun v hv => ⟨(hψ v hv).1.comp (continuous_apply ()),
      (hψ v hv).2.comp_homeomorph (Homeomorph.funUnique Unit (Fv F v))⟩)
  rw [integral_unitVec_eq li G,
    Finset.prod_congr rfl (fun v _ => haveI := hsf v; integral_unitVec_eq (lam v) (ψ v))] at key
  simp only [Fintype.card_unit, mul_one] at key
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hpow : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0))) :=
      ((continuous_pow _).mul continuous_const).tendsto 0
    rw [zero_pow hd.ne', zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsub := key.sub hpow
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc (fun v hv => (hψ v hv).2) ε hε
  have h0mem : (0 : F) ∈ IntOut T := fun v _ => by
    rw [map_zero]
    exact zero_mem _
  have e := (tsum_unitVec_eq T (fun x => G (θ ε * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x))).trans (tsum_eq_zero_add_of_finset _ B hB hh)
  rw [Set.indicator_of_mem h0mem] at e
  rw [e]
  simp only [truncSum, map_zero, mul_zero]
  ring

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.tate_shafarevich_transport : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ShaG φ' hφ' χ' ρ' → ShaG φ hφ χ ρ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | exact GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.poitou_tate_sequence_transport : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ∀ (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R) (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R) (hρ : ContAction ρ) (hρ' : ContAction ρ'), (∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))), (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) → j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z)) → NineG φ' hφ' χ' j' ρ' hρ' → NineG φ hφ χ j ρ hρ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso | exact GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso | (intros; apply GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_add : GlobalTheory.CompanionTheory.GrForm.StAdd := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAdd | exact GlobalTheory.CompanionTheory.GrForm.stAdd | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAdd <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_cover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | exact GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | (intros; apply GlobalTheory.CompanionTheory.GrForm.AffCover.stCover <;> assumption)
end
