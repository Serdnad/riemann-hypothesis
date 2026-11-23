module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightFlagPieceTriangularFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle194
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle196
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.height_flag_piece_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (n m : ℕ) (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ) (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ), PlaceMatch φ P X → (∀ v, IsUnit (P v)) → ∀ (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → ∀ U : ι → ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, (∀ v, Biorth r m (U v) (fun b => (U v b)ᴴ)) → (∀ v k y, y ∈ locFlag (φ v) (P v) F k ↔ ∀ b, k ≤ b → (U v b)ᴴ *ᵥ y = 0) → ∀ b, covStd (r b) (Λ b) * ∏ v, ‖((U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v))).det‖ ^ 2 = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * r b) * pieceHt X F b := by
  first | exact @GlobalTheory.PieceCov.main | exact GlobalTheory.PieceCov.main | (intros; apply GlobalTheory.PieceCov.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem hform_eq_star_dotProduct (I : AutInst) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = star x ⬝ᵥ (I.J *ᵥ y) := by
  change (∑ i, ∑ j, star (x i) * I.J i j * y j) = _
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem IsPerp.exists_split {I : AutInst} {D : Sib I} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin D.n) I.E} {xf : I.Gf} (h : IsPerp D s x A xf) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I (1, xf)) : ∃ a : 𝓞 I.E, ∃ w ∈ D.L, y = a • x + A *ᵥ w := by
  obtain ⟨hn, hβ, hxA, hAJ, hx, hL⟩ := h
  have hJ : I.Jᴴ = I.J := by
    rw [← (show Formalism.UG.cT (starRingEnd I.E) I.J = I.Jᴴ by ext i j; rfl)]
    exact I.J_herm
  have hsq : sgn I.E s * sgn I.E s = 1 := by cases s <;> simp [sgn]
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    intro h0
    rw [hβ] at h0
    rw [h0, zero_mul] at hsq
    exact zero_ne_one hsq
  obtain ⟨u, A', -, -, -, -, hres, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ

  have hdec : y = (u ⬝ᵥ y) • x + A *ᵥ (A' *ᵥ y) := by
    have h1 : (vecMulVec x u + A * A') *ᵥ y = y := by rw [hres, one_mulVec]
    rw [add_mulVec, ← mulVec_mulVec] at h1
    refine h1.symm.trans ?_
    congr 1
    ext i
    simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  have hpair : ∀ (c : I.E) (w : Fin D.n → I.E), y = c • x + A *ᵥ w →
      star x ⬝ᵥ (I.J *ᵥ y) = c * sgn I.E s := by
    intro c w e
    rw [e, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hβ, mulVec_mulVec,
      dotProduct_mulVec, hxA, zero_dotProduct, add_zero]
  have hcoef : u ⬝ᵥ y = sgn I.E s * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
    rw [hform_eq_star_dotProduct, hpair _ _ hdec]
    linear_combination (-(u ⬝ᵥ y)) * hsq
  have hint : Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range :=
    (((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.2.1 y).mp hy) x hx
  have hsgn : sgn I.E s ∈ (algebraMap (𝓞 I.E) I.E).range := by
    cases s
    · exact ⟨-1, by simp [sgn]⟩
    · exact ⟨1, by simp [sgn]⟩
  obtain ⟨a, ha⟩ := Subring.mul_mem _ hsgn hint
  have hca : (u ⬝ᵥ y) • x = a • x := by rw [hcoef, ← ha, algebraMap_smul]
  refine ⟨a, A' *ᵥ y, (hL _).mpr ?_, ?_⟩
  · have e : A *ᵥ (A' *ᵥ y) = y - a • x := by
      rw [← hca]
      exact eq_sub_of_add_eq' hdec.symm
    rw [e]
    exact Submodule.sub_mem _ hy (Submodule.smul_mem _ a hx)
  · rw [← hca]
    exact hdec

theorem afVec_mulVec_eq_afMat_mulVec (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) (w : Fin k → I.E) :
    afVec I (A *ᵥ w) = afMat I A *ᵥ afVec I w := by
  funext i

  simp [afVec, afMat, mulVec, dotProduct, map_sum]

private theorem mem_lf_iff_mem_latS (I : AutInst) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    v ∈ I.Lf ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
  show v ∈ lamAf (F := I.F) I.L ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L
  unfold lamAf Formalism.UG.latS
  constructor
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem adelicLattice_split : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, I.fmat xf⁻¹ *ᵥ z ∈ I.Lf ↔ ∃ a ∈ IntAf I.F I.E, ∃ w ∈ D.inst.Lf, z = a • afVec I x + afMat I A *ᵥ w := by
  intro I D s x A xf h z
  have hmem : ∀ y : Fin I.n → I.E, y ∈ lamX I (1, xf) → I.fmat xf⁻¹ *ᵥ afVec I y ∈ I.Lf :=
    fun y hy => ((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).1 y).mp hy
  obtain ⟨-, -, -, -, hx, hL⟩ := id h
  constructor
  · intro hz
    have hspan := Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds I.L
      (Module.Finite.iff_fg.mpr I.L_fg) I.L_span (xf : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) z
      ((mem_lf_iff_mem_latS I _).mp hz)
    clear hz
    induction hspan using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      have hy' : y ∈ lamX I (1, xf) := by
        rw [GlobalTheory.PointLattice.lamX_eq_globLat]
        exact hy
      obtain ⟨a0, w0, hw0, e⟩ := IsPerp.exists_split h hy'
      refine ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a0), Formalism.UG.CS.incl_int a0,
        afVec I w0, Submodule.subset_span ⟨⟨w0, hw0⟩, rfl⟩, ?_⟩
      rw [← afVec_mulVec_eq_afMat_mulVec]
      funext i
      simp [afVec, e, Algebra.smul_def, map_add (f := _), map_mul]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add v1 v2 _ _ h1 h2 =>
      obtain ⟨a1, ha1, w1, hw1, rfl⟩ := h1
      obtain ⟨a2, ha2, w2, hw2, rfl⟩ := h2
      refine ⟨a1 + a2, add_mem ha1 ha2, w1 + w2, add_mem hw1 hw2, ?_⟩
      rw [add_smul, mulVec_add]
      abel
    | smul c v _ h1 =>
      obtain ⟨a, ha, w, hw, rfl⟩ := h1
      refine ⟨(c : I.E ⊗[I.F] Af I.F) * a, mul_mem c.2 ha, (c : I.E ⊗[I.F] Af I.F) • w,
        Submodule.smul_mem _ c hw, ?_⟩
      show (c : I.E ⊗[I.F] Af I.F) • (a • afVec I x + afMat I A *ᵥ w) = _
      rw [smul_add, mul_smul, mulVec_smul]
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mulVec_add, mulVec_smul]
    refine add_mem (Submodule.smul_mem I.Lf ⟨a, ha⟩ (hmem x hx)) ?_
    have hw' : w ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun y : D.L => afVec I (y : Fin D.n → I.E)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hv
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ afVec I y) ∈ I.Lf
      rw [← afVec_mulVec_eq_afMat_mulVec]
      exact hmem _ ((hL y).mp hy)
    | zero => simp
    | add v1 v2 _ _ h1 h2 =>
      rw [mulVec_add, mulVec_add]
      exact add_mem h1 h2
    | smul c v _ h1 =>
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v)) ∈ I.Lf
      rw [mulVec_smul, mulVec_smul]
      exact Submodule.smul_mem I.Lf c h1

end GlobalTheory.StabUnfold
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ v, qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧ star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧ (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  first | exact @GlobalTheory.StabUnfold.isPerp_at_place | exact GlobalTheory.StabUnfold.isPerp_at_place | (intros; apply GlobalTheory.StabUnfold.isPerp_at_place <;> assumption)
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov
end
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefMeas

theorem image_meas {ι X Y Z : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Z) (c : X → Y) (hc : Measurable c) (hi : Function.Injective c)
    (a : Z → ι → X) (ha : MeasurePreserving a ν (Measure.pi fun _ : ι => μ)) (hai : Function.Injective a)
    (S : Set Z) (hS : MeasurableSet S) :
    MeasurableSet ((fun p v => c (a p v)) '' S) ∧
      Measure.pi (fun _ : ι => μ.map c) ((fun p v => c (a p v)) '' S) = ν S := by
  have he : MeasurableEmbedding c := hc.measurableEmbedding hi
  haveI : SigmaFinite (μ.map c) := he.sigmaFinite_map
  have h1 : MeasurePreserving (fun (q : ι → X) (v : ι) => c (q v)) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ.map c) :=
    measurePreserving_pi _ _ fun _ => ⟨hc, rfl⟩
  have h2 : MeasurePreserving (fun (p : Z) (v : ι) => c (a p v)) ν (Measure.pi fun _ : ι => μ.map c) := h1.comp ha
  have hinj : Function.Injective (fun (p : Z) (v : ι) => c (a p v)) := fun p q h =>
    hai (funext fun v => hi (congrFun h v))
  have hm : MeasurableSet ((fun p v => c (a p v)) '' S) := hS.image_of_measurable_injOn h2.measurable hinj.injOn
  refine ⟨hm, ?_⟩
  rw [← h2.measure_preimage hm.nullMeasurableSet, Set.preimage_image_eq _ hinj]

theorem box_meas : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  intro ι _ k r j β hm hβ hat F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄ Ω hΩ
  obtain ⟨hl, -, hinj, -⟩ := Swap.range_eq_and_injective_parabolic_unipotent_product k r j β hm hβ
  haveI s1 : SigmaFinite (volume : Measure (Swap.STop r j)) := Measure.prod.instSigmaFinite
  haveI s2 : SigmaFinite (volume : Measure (PTop k r j)) := Measure.prod.instSigmaFinite
  haveI s3 : SigmaFinite (volume : Measure ((UTin β → ℂ) × PTop k r j)) := Measure.prod.instSigmaFinite
  haveI b1 : BorelSpace (Swap.STop r j) := Prod.borelSpace
  haveI b2 : BorelSpace (PTop k r j) := Prod.borelSpace
  haveI b3 : BorelSpace ((UTin β → ℂ) × PTop k r j) := Prod.borelSpace
  have hG : Continuous fun q : (UTin β → ℂ) × PTop k r j =>
      (Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1)) : Mt k r) :=
    (Swap.cont_pTop.comp continuous_snd).matrix_mul ((GlobalTheory.Amp.Swap.cont_uEmb k r).comp
      ((Swap.extZ (fun p : UT r => β p.1.1 = β p.1.2) ℂ).continuous_of_finiteDimensional.comp continuous_fst))
  have hS : MeasurableSet ((Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) : Set (Crd ι k r j β)) :=
    (MeasurableSet.univ_pi h₁).prod ((MeasurableSet.univ_pi h₂).prod ((MeasurableSet.univ_pi h₃).prod (MeasurableSet.univ_pi h₄)))
  haveI d1 : StandardBorelSpace (Swap.STop r j) := StandardBorelSpace.prod
  haveI d2 : StandardBorelSpace (PTop k r j) := StandardBorelSpace.prod
  haveI d3 : StandardBorelSpace ((UTin β → ℂ) × PTop k r j) := StandardBorelSpace.prod
  haveI d4 : StandardBorelSpace (Mt k r) := StandardBorelSpace.pi_countable
  haveI d5 : StandardBorelSpace (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)) := StandardBorelSpace.prod
  haveI d6 : StandardBorelSpace ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) := StandardBorelSpace.pi_countable
  haveI d7 : StandardBorelSpace (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := StandardBorelSpace.prod
  haveI d8 : StandardBorelSpace (Crd ι k r j β) := StandardBorelSpace.prod
  have key := image_meas (volume : Measure ((UTin β → ℂ) × PTop k r j)) volume _ hG.measurable
    (Matrix.of.symm.injective.comp hinj) atP hat usage₂.1 _ hS
  rw [← hl] at key
  subst hΩ
  refine ⟨key.1, key.2.trans ?_⟩
  haveI t1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) :=
    Measure.prod.instSigmaFinite
  haveI t3 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t4 : SigmaFinite (volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)) := Measure.pi.sigmaFinite _
  haveI t2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) :=
    Measure.prod.instSigmaFinite
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi]

end GlobalTheory.DegVol.RefMeas
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧ ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagMem.lowers_keeps | exact GlobalTheory.IwConst.FlagMem.lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagMem.lowers_keeps <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r → ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  first | exact @GlobalTheory.IwConst.CloseLevi.close_levi | exact GlobalTheory.IwConst.CloseLevi.close_levi | (intros; apply GlobalTheory.IwConst.CloseLevi.close_levi <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.tendsto_rescaled_measure_gauge_unit_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  first | exact @GlobalTheory.IwConst.VagBody.tendsto_body | exact GlobalTheory.IwConst.VagBody.tendsto_body | (intros; apply GlobalTheory.IwConst.VagBody.tendsto_body <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ g ∈ S, nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by
  first | exact @GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | exact GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | (intros; apply GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | exact GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.IwTangent.lie_algebra_of_isCut | exact GlobalTheory.IwTangent.lie_algebra_of_isCut | (intros; apply GlobalTheory.IwTangent.lie_algebra_of_isCut <;> assumption)
end
