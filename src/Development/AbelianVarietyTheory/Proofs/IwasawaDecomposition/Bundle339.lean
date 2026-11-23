module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle327
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  first | exact @GlobalTheory.Mem.LiftGrow.growth_pair | exact GlobalTheory.Mem.LiftGrow.growth_pair | (intros; apply GlobalTheory.Mem.LiftGrow.growth_pair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.petersson_normSq_pos_automorphicFunction_unitary : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsQuot V μ 𝓕 → ∀ φ, IsAutFun V φ → φ ≠ 0 → IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ → 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  first | exact @GlobalTheory.Mem.PetPos.petersson_pos | exact GlobalTheory.Mem.PetPos.petersson_pos | (intros; apply GlobalTheory.Mem.PetPos.petersson_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) := by
  first | exact @GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | (intros; apply GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  first | exact @GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | exact GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | (intros; apply GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Crd

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Ortho (S : Formalism.BasicNotions.HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem ortho_pos (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) : Ortho (Examples₂.posSpace hstar N) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) N 0 a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

abbrev co (S : Formalism.BasicNotions.HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem Ortho.isStd {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) : Formalism.L2.Herm.IsStd S := ⟨S.frame, h.1, h.2⟩

theorem Ortho.gram {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) :
    S.gram.reindex (finCongr hn) (finCongr hn) = 1 := by
  subst hn
  ext a b
  simpa [HSpace.gram, Matrix.one_apply] using h.1 a b

theorem Ortho.mem_standardLattice_iff_integral_coords {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) (x : Fin n → E) :
    x ∈ S.L0.map (((co S hn : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
      ∀ j, x j ∈ (algebraMap (𝓞 E) E).range := by
  subst hn
  rw [h.2]
  constructor
  · rintro ⟨v, hv, rfl⟩ j
    have := (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame v).1 hv j
    simpa [co] using this
  · intro hx
    refine ⟨(co S rfl).symm x, (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame _).2 fun j => ?_, (co S rfl).apply_symm_apply x⟩
    have h2 : S.frame.repr ((co S rfl).symm x) j = x j :=
      congrFun ((co S rfl).apply_symm_apply x) j
    rw [h2]
    exact hx j

theorem map_symm_map {S : Formalism.BasicNotions.HSpace E} {n : ℕ} (e : S.V ≃ₗ[E] (Fin n → E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    (L.map ((e.symm : (Fin n → E) →ₗ[E] S.V).restrictScalars (𝓞 E))).map
      ((e : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = L := by
  ext x
  simp

theorem incl_co {S S' : Formalism.BasicNotions.HSpace E} {n : ℕ} (hn : S.rank = n) (hn' : S'.rank = n - 1) (f : S'.V →ₗ[E] S.V)
    (hf : ∀ (a : Fin S'.rank) (b : Fin S.rank), (a : ℕ) = b → f (S'.frame a) = S.frame b) (x : Fin (n - 1) → E) (j : Fin n) :
    co S hn (f ((co S' hn').symm x)) j = if h : j.1 < n - 1 then x ⟨j.1, h⟩ else 0 := by
  subst hn
  have hs : (co S' hn').symm x = ∑ a : Fin (S.rank - 1), x a • S'.frame (finCongr hn'.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k

    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [co]
    · intro a _ ha
      have : ¬ (a : ℕ) = k := fun h => ha (Fin.ext h)
      simp [co, Finsupp.single_apply, Fin.ext_iff, this]
    · simp
  have hb : ∀ a : Fin (S.rank - 1), f (S'.frame (finCongr hn'.symm a)) = S.frame ⟨a.1, by omega⟩ := fun a => hf _ _ rfl

  rw [hs, map_sum, map_sum]
  simp only [map_smul, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ a : Fin (S.rank - 1), co S rfl (S.frame ⟨a.1, by omega⟩) j = if a.1 = j.1 then 1 else 0 := by
    intro a
    simp [co, Fin.ext_iff]
  simp only [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg (fun h2 => ha (Fin.ext h2)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun h2 : a.1 = j.1 => h (h2 ▸ a.2)), mul_zero]

end Gen

end GlobalTheory.Mem.Col2.Crd

end



theorem GlobalTheory.Mem.Col2.TC.spaces_in_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  intro B X I hI hP l Z
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact Crd.ortho_pos hs _
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  refine ⟨⟨fun i _ => (oX i).isStd, oX'.isStd⟩, oX'.gram (rankP (I.rec7 l Z)), fun x j => ?_, fun i hi =>
    ⟨(oX i).gram (rankN (I.rec7 l Z) i hi), fun x => (oX i).mem_standardLattice_iff_integral_coords (rankN (I.rec7 l Z) i hi) x, fun u a => ⟨fun c => ?_, ?_⟩⟩⟩
  · exact Crd.incl_co (S := B.sp.X B.R.m) (S' := B.sp.X') (rankN (I.rec7 l Z) _ le_rfl) (rankP (I.rec7 l Z)) B.sp.iX' hP.iX x j
  · unfold TC.latAt
    rw [dite_eq_left hi]
    exact Crd.map_symm_map (S := B.sp.X i) (TC.crd B i hi) _
  · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl⟩
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat


open GlobalTheory.Mem.Col2.TC.PsiRat in
theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section Same

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure SameG {y : Ys X n} (p p' : PtY ST SG Q y) : Prop where
  fr : p'.1.1.1.2 = p.1.1.1.2
  ys : p'.1.2 = p.1.2
  at_eq : ∀ w : SG, p'.1.1.deco.1.at w.1 = p.1.1.deco.1.at w.1
  be : p'.1.1.deco.1.be = p.1.1.deco.1.be

theorem SameG.refl {y : Ys X n} (p : PtY ST SG Q y) : SameG p p :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

private theorem locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
  have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
  have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl

  have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
    intro M x
    rw [hmemL, hmemL]
    constructor
    · rintro ⟨s, hs0, hx⟩
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hz' : z = g.symm (s • x) := by
        rw [← hzx]
        simp
      exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
    · rintro ⟨s, hs0, hx⟩
      refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
  ext x
  rw [hmemg, hmemg, h]

theorem SameG.smul {y : Ys X n} {Λ : LevFam X.E X.K n SG} {Θ : LevQFam X.E X.K n Q} (h : FrmG Λ Θ) {p p' : PtY ST SG Q y}
    (r : SameG p p') : SameG ((ptYAct y Λ Θ).toSMul.smul h p) ((ptYAct y Λ Θ).toSMul.smul h p') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun F => fun P => (FrmG.incl Λ Θ h).1.1 * F P * ((FrmG.incl Λ Θ h).2.2 P)⁻¹.1) r.fr
  · exact congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
  · intro w
    show Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p'.1.1.deco.1.N) =
      Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p.1.1.deco.1.N)
    exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
  · exact congrArg (fun B => fun w x => ((FrmG.incl Λ Θ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be

theorem SameG.dn {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) :
    SameG p (p.mv (p.1.1.deco.dn P f')) := by
  classical
  unfold PtY.mv
  refine Eq.mpr (apply_dite (SameG p) _ _ _) ?_
  split
  · refine ⟨rfl, rfl, fun w => ?_, ?_⟩
    · show (p.1.1.deco.dn P f').1.at w.1 = p.1.1.deco.1.at w.1
      unfold DecoSet.dn
      split_ifs with hok
      · exact ((p.1.1.deco.2.dnN_spec P hP.ne).2.2.1 w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
      · rfl
    · show (p.1.1.deco.dn P f').1.be = p.1.1.deco.1.be
      unfold DecoSet.dn
      split_ifs <;> rfl
  · exact SameG.refl p

end Same

section Coset

private theorem cosetIn_eq_of_sameG' {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q := by
  have hfr : ∀ P, frsF sel mu q'.1.1 P = frsF sel mu q.1.1 P := by
    intro P
    unfold frsF
    split_ifs with hP
    · unfold Deco.liftFr
      rw [r.at_eq ⟨P.1, hP⟩, r.be]
    · exact congrFun r.fr _
  funext P
  unfold cosetIn
  rw [r.ys, hfr P]


open Classical GlobalTheory.TopStep in
theorem cosetIn_eq_of_sameG {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (hX : X.Ok) (hPr : Pr.Ok)
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q :=
  cosetIn_eq_of_sameG' r

end Coset

section Normal

theorem prefRep_pref {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D)
    (h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p) : pref (prefRep pref q) := by
  unfold prefRep
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem GStep.NormalFor.eq {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} {b : S.β} {f : S.D b → A}
    {q q' : S.D b} (hq : S.NormalFor b f q) (hq' : S.NormalFor b f q')
    (h : ∀ r, (∃ g : S.G b, r = f (g • q)) ↔ ∃ g : S.G b, r = f (g • q')) : f q = f q' := by
  unfold GStep.NormalFor at hq hq'
  rw [hq, hq']
  exact congrArg (@Classical.epsilon A ⟨f q⟩) (funext fun r => propext (h r))

theorem GStep.exists_normalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have hex : ∃ r, ∃ g : S.G b, r = f (g • q) := ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := Classical.epsilon_spec hex
  refine ⟨g, ?_⟩
  have hset : (fun r => ∃ g : S.G b, r = f (g • q)) = (fun r => ∃ g' : S.G b, r = f (g' • g • q)) := by
    funext r
    apply propext
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g, by rw [mul_smul]⟩
  unfold GStep.NormalFor
  exact hg.symm.trans (congrArg (@Classical.epsilon A ⟨f q⟩) hset)

theorem GStep.prefRep_eq_of_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hn : ∀ q : MulAction.orbitRel.Quotient (S.G b) (S.D b), S.NormalFor b f (prefRep pf q)) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) (d' : S.D b)
    (hd : ∀ h : S.G b, f (h • d') = f (h • prefRep pf q)) :
    f (prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d')) = f (prefRep pf q) := by
  obtain ⟨k, hk⟩ : ∃ k : S.G b, k • d' = prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d') :=
    Quotient.exact (prefRep_spec pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d'))
  refine GStep.NormalFor.eq (hn _) (hn q) fun r => ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k, by rw [← hk, ← mul_smul, hd]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k⁻¹, by rw [← hd, ← hk, mul_smul, inv_smul_smul]⟩

theorem GStep.prefRep_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hpf : ∀ p, pf p → S.NormalFor b f p) (hnp : ∀ p, S.NormalFor b f p → pf p)
    (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.NormalFor b f (prefRep pf q) := by
  obtain ⟨g, hg⟩ := GStep.exists_normalFor S b f (Quotient.out q)
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) p = q ∧ pf p :=
    ⟨g • Quotient.out q, (Quotient.sound (s := MulAction.orbitRel (S.G b) (S.D b)) (MulAction.mem_orbit _ g)).trans
      (Quotient.out_eq q), hnp _ hg⟩
  exact hpf _ (prefRep_pref pf q hex)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.pref_of_normalFor (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m) (b : (I.stp0 u a j).β) (p : (I.stp0 u a j).D b)
    (h : (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') p) : I.pref u a j b p := by
  have hm := B.R.two_le_m
  refine ⟨fun h0 => absurd hj (by omega), fun _ => h, ?_⟩
  show ∀ h : j = B.R.m, _
  intro hjm
  exact absurd hjm (by omega)

private theorem TC.cosetIn_rep_cl_dn_eq (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (f : Sp B.fields.E (B.R.N i) → Res v.1) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).dn c.1 ((I.stp u a i).rep c) v f))) =
      cosetIn ((I.stp u a i).rep c) := by
  obtain ⟨b, q⟩ := c
  have r0 : SameG ((I.stp u a i).rep ⟨b, q⟩) (((I.atIn u a).A i).dn b ((I.stp u a i).rep ⟨b, q⟩) v f) :=
    SameG.dn _ v (moveHyp_of_ok hPr u v) f
  by_cases hi : i + 1 = B.R.m
  · exact GStep.prefRep_eq_of_normal (I.stp0 u a i) b (fun q' => cosetIn q') (I.pref u a i b)
      (GStep.prefRep_normal (I.stp0 u a i) b _ (I.pref u a i b) (fun p hp => hp.2.1 hi)
        (fun p hp => I.pref_of_normalFor u a i hi b p hp)) q _
      (fun h => cosetIn_eq_of_sameG' (SameG.smul h r0))
  ·
    have hemp : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn p = fun _ => ∅ := by
      intro p
      have hys : ∀ (Y : Set (Sp B.fields.E (B.R.N i))) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))),
          Y ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) i).ys N → Y = ∅ := by
        intro Y N hY
        unfold ysAt at hY
        rw [if_neg hi] at hY
        exact hY
      have hp : p.1.2 = ∅ := hys _ _ p.2
      funext P
      unfold cosetIn
      rw [hp]
      ext z
      simp
    exact (hemp _).trans (hemp _).symm

end Normal

theorem TC.dn_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K eY eV L hK _ _ _ v β c g _

  obtain ⟨k, hR⟩ := hK
  exact ((hR.key ((I.fm l u a).dn i v c.1 g) c.1).mpr ⟨rfl, I.cosetIn_rep_cl_dn_eq l.pr u a i v c.1 _⟩).trans c.2

end GlobalTheory.Mem.Col2
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def eWt (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) :=
  LinearEquiv.refl ℂ _

theorem eWt_apply (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (z : (I.per l u a).Wrow)
    (c : (I.fm l u a).clsP) (s : Formalism.L2.Forms.FrP (I.rec7 l Z)) (s' : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1))
    (h : s'.1 = s.1) : eWt I l Z u a z c s = z c s' := by
  have e : s' = s := Subtype.ext h
  subst e
  rfl

end GlobalTheory.Mem.Col2.TwP

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

noncomputable def clDown {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i)
    (c : (I.stp u a i).Cl) : (I.stp u I.mu0 i).Cl :=
  (I.stp u I.mu0 i).cl (Idx.top I.sel (I.tup I.mu0) (I.idx I.mu0) (le_of_lt hi))
    ⟨(extTo (I.Q I.mu0) ((I.stp u a i).rep c).1.1, ∅), by
      rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)]
      rfl⟩

theorem nonempty_clDown : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i →
    Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) :=
  fun I _ u a i hi => ⟨I.clDown u a i hi⟩

end GlobalTheory.Mem.Col2.TC
end
