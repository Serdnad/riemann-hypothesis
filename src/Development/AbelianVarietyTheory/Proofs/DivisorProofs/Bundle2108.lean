module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameter
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaKeyRule_value_classicalNormalForm : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  first | exact @GlobalTheory.MBLow.Cl.key_value_of_nf | exact GlobalTheory.MBLow.Cl.key_value_of_nf | (intros; apply GlobalTheory.MBLow.Cl.key_value_of_nf <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extremalVector_eval_multiplicitySpace_onto_holomorphic : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → WtIs M w → ∀ v : M.Vec, IsExtVec M v → ∀ χ : GA D V → ℂ, (∀ k ∈ Kf, χ k = 1) → (∀ P ∈ Formalism.L2.Pj.holSub0 X la, ∃ T ∈ Mult θ M (Kf : Set (GA D V)) χ, T v = adel V dict (muPin V dict mu c) P) ∧ ∀ T ∈ Mult θ M (Kf : Set (GA D V)) χ, ∃ P ∈ Formalism.L2.Pj.holSub0 X la, adel V dict (muPin V dict mu c) P = T v := by
  first | exact @GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 | exact GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 | (intros; apply GlobalTheory.HolDict.mult_eval_eq_adel_holSub0 <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ArchCoordsD


open GlobalTheory.FockVacuum in
theorem herm_rot_pos {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b *
      star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith


open GlobalTheory.FockVacuum in
theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]

    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_rot_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoordsD
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.FockVacuum

noncomputable section

namespace GlobalTheory.HoweD

section Sign

variable {ι : Type} {P Q R S : ι → ℕ}

def cplxD (ι : Type) (P Q R S : ι → ℕ) : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

theorem cplxD_apply (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

theorem cplxD_cplxD (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) : cplxD ι P Q R S (cplxD ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]

theorem herm_cplxD [Fintype ι] (c c' : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplxD ι P Q R S c w a b * star (cplxD ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

theorem herm_cplxD_pos [Fintype ι] (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

theorem cplxD_single [DecidableEq ι] (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := by
  ext w' a' b'
  rw [cplxD_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

theorem exists_vacuumD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]

    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD
    (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplxD _ P Q R S c = (lineSign a b).re • c' := cplxD_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplxD _ P Q R S c) x
  rw [cplxD_cplxD] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.HoweD
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → At (evI F) ((h.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @GlobalTheory.HoweD.deriv_charD | exact GlobalTheory.HoweD.deriv_charD | (intros; apply GlobalTheory.HoweD.deriv_charD <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.bi_invariant_conjugacy_classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero | exact GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localComponent_levelFixedVectors_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocFix.fixed_ne_bot | exact GlobalTheory.BCT.LocFix.fixed_ne_bot | (intros; apply GlobalTheory.BCT.LocFix.fixed_ne_bot <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_cols_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g C' D' Z' hC hZ hD
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  dsimp only [adMat] at hC hZ hD
  set ι := inclR (F := F) (E := E) (AF F) with hι
  set x : Matrix (Fin n) (Fin n) E := C' * (cT (σ : E →+* E) D * J) + Z' * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    D' * (cT (σ : E →+* E) C * J) with hx
  have hM : (matHom _ σ J g).1 = x.map ι := by
    calc (matHom _ σ J g).1
        = (matHom _ σ J g).1 * (C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
            D * (cT (σ : E →+* E) C * J)).map ι := by
          rw [hF.sum, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      _ = x.map ι := by
          rw [hx]
          simp only [Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.mul_add, ← Matrix.mul_assoc]
          rw [hC, hZ, hD]
  have hdet : x.det ≠ 0 := by
    haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨ι 0, ι 1, fun e => zero_ne_one (hinj e)⟩⟩
    intro h0
    have hu : IsUnit (x.map ι).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := ι.map_det x
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) x * J * x = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have hcT : cT (sigR (AF F) σ) (x.map ι) = (cT (σ : E →+* E) x).map ι := by
    ext a b; simp [Formalism.UG.cT, sigR, hι, inclR]
  rw [hM, hcT, JR, ← hι, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end GlobalTheory.SphEis
end
