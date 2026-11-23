module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev Lines (P Q R S : ι → ℕ) := Σ o : (Σ w : ι, Ix (P w) (Q w)), Ix (R o.1) (S o.1)

def lineSgn (n : Lines P Q R S) : Bool :=
  linePos (p := P n.1.1) (q := Q n.1.1) (r := R n.1.1) (s := S n.1.1) (n.1.2, n.2)

theorem blockDiagonal'_mulVec_apply {m : (Σ w : ι, Ix (P w) (Q w)) → Type} [∀ o, Fintype (m o)]
    [∀ o, DecidableEq (m o)] (M : ∀ o, Matrix (m o) (m o) ℂ) (v : (Σ o, m o) → ℂ) (o : Σ w : ι, Ix (P w) (Q w))
    (b : m o) : (blockDiagonal' M *ᵥ v) ⟨o, b⟩ = ∑ b', M o b b' * v ⟨o, b'⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · simp [blockDiagonal'_apply']
  · intro o' _ h
    simp [blockDiagonal'_apply_ne M b _ (Ne.symm h)]
  · simp

theorem diagonal_lineSgn : (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) =
    blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => Jm (P o.1) (Q o.1) o.2 o.2 • Jm (R o.1) (S o.1) := by
  ext ⟨o, b⟩ ⟨o', b'⟩
  by_cases h : o = o'
  · subst h
    rcases o with ⟨w, a⟩
    rw [blockDiagonal'_apply']
    rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
      simp [diagonal_apply, Jm, Formalism.UG.Jpq, lineSgn, linePos, Matrix.one_apply] <;> split_ifs <;> simp_all
  · rw [blockDiagonal'_apply_ne _ _ _ h, diagonal_apply_ne]
    intro e
    exact h (congrArg Sigma.fst e)

theorem blockDiagonal'_mem (M : ∀ w, Mat (R w) (S w)) (hM : ∀ w, (M w)ᴴ * Jm (R w) (S w) * M w = Jm (R w) (S w)) :
    (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1)ᵀ *
        (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) *
        (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1).map star =
      diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1 := by
  rw [diagonal_lineSgn, blockDiagonal'_transpose, blockDiagonal'_map _ _ (star_zero ℂ), ← blockDiagonal'_mul,
    ← blockDiagonal'_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, GlobalTheory.SchrodOsc.Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end GlobalTheory.HoweD.Osc

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} {G : Type} [Group G]

abbrev lineNum (P Q R S : ι → ℕ) := GlobalTheory.SchrodOsc.signEquiv (lineSgn (P := P) (Q := Q) (R := R) (S := S))

abbrev NumIx (P Q R S : ι → ℕ) :=
  Fin (Fintype.card {n // lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true})

def blockHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (Lines P Q R S) (Lines P Q R S) ℂ where
  toFun g := blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal'_one
  map_mul' g g' := by simp [blockDiagonal'_mul]

def numHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (NumIx P Q R S) (NumIx P Q R S) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (∀ w, Mat (R w) (S w))) (g : G) :
    numHom P Q k g = reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (∀ w, Mat (R w) (S w))) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w))
    (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, GlobalTheory.SchrodOsc.fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)).map star =
      reindex (lineNum P Q R S) (lineNum P Q R S)
        ((blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal'_mem _ (hk g)]

def unitHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w, Mat (R w) (S w)))
    (hc : Continuous k) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :
    Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun (o : Σ w : ι, Ix (P w) (Q w)) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

def coordOf (z : NumIx P Q R S → ℂ) : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum P Q R S ⟨⟨w, a⟩, b⟩)

theorem coordOf_add (z z' : NumIx P Q R S → ℂ) : coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : NumIx P Q R S → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Lines P Q R S → ℂ := fun n => (if lineSgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F ⟨⟨w, a⟩, b⟩ := by
    intro w a b
    simp only [coordOf, F, star_mul, lineSgn, GlobalTheory.SchrodOsc.lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F ⟨⟨w, a⟩, b⟩ := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inl, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inr,
    Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) (g : G) (z : NumIx P Q R S → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [coordOf, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [blockDiagonal'_mulVec_apply]
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Function.comp_apply]
  exact Finset.sum_congr rfl fun _ _ => by simp only [coordOf, transpose_apply]; ring

end GlobalTheory.HoweD.Osc

open GlobalTheory.HoweD

theorem GlobalTheory.HoweD.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.HoweD.Osc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.HoweD.Osc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add (f := _), ← GlobalTheory.HoweD.Osc.coordOf_add, hφ, ← GlobalTheory.HoweD.Osc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.HoweD.Osc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.HoweD.Osc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.HoweD.Osc.coordOf (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : GlobalTheory.HoweD.Osc.Lines P Q R S => c n.1.1 n.1.2 n.2)
      ((GlobalTheory.HoweD.Osc.lineNum P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp only [GlobalTheory.HoweD.Osc.coordOf]
    rw [Equiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have h := hω₀ (GlobalTheory.HoweD.Osc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.HoweD.Osc.coordOf_mulVec, hz] at h
  exact h
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  first | exact @GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | exact GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | (intros; apply GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuous_thetaTransform_adelicSchwartz : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  first | exact @GlobalTheory.ThetaTrCont.continuous_thetaTr | exact GlobalTheory.ThetaTrCont.continuous_thetaTr | (intros; apply GlobalTheory.ThetaTrCont.continuous_thetaTr <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaQuasiRatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_cAF' (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : cA σ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sum_three_fintype_reverse_order {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplOF' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) (x y : WOF F E nS nT) :
    symp (cA σ) ξ (incM F JA) (incM F JB) x y = symplOF σ JS JT ξ₀ x y := by
  have hB' : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := F) (AF F) (ξ₀ * JS⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM F JA i k = incAF F E (JT k i) := by
    intro i k; subst hA; rfl
  unfold symp hTens symplOF hOF
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_three_fintype_reverse_order]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_cAF']
  calc ξ * (x i j * incAF F E (JT k i) * incM F JB j l * cAF σ (y k l))
      = x i j * incAF F E (JT k i) * (ξ * incM F JB j l) * cAF σ (y k l) := by ring
    _ = _ := by rw [hB']; ring

theorem thetaTr_ratWF_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratWF γ = incM F γ := rfl
  have hform := co.form (incM F γ) w
  rw [symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF F) × (κ → AF F) :=
    (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu
  set v := co.e w
  have law := GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ
  have hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr B.ψ (u + v) Φ =
      B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr B.ψ u (GlobalTheory.WeilM.schr B.ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1 y z, ← hu,
    symplOHF, hform, h2]

end GlobalTheory.ThetaQuasiRatF
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.ThetaTrContF

theorem continuous_thetaTrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc

end GlobalTheory.ThetaTrContF
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB GlobalTheory.CxPts GlobalTheory.Published

namespace GlobalTheory.SelfCont

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem icls_fnB_add {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem isConj_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_add (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)
    fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_add (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

variable [IsIntegral X] {D : ℕ} {t : ℝ → ℝ} {u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ}


omit [IsIntegral X] in
theorem isometric_comb_raise {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p) (n : Fin 2 → ℤ) :
    (comb ![fnB v hv hc, N] n).Isometric ((zp N (n 1)).raise (fun σ y => (n 0 : ℝ) * v σ y)
      (fun σ y => (hv σ y).const_mul _) (isConj_mul hc _)) :=
  icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_fnB_mul hv hc, icls_zp, icls_comb,
      Fin.sum_univ_two, add_comm]
    rfl)

theorem mixed_eq (H : ArCalc) (hX : IsArithVar p D) {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p)
    {Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ} (hΘ : IsArFun ![fnB v hv hc, N] D Θ) (n : Fin 2 → ℤ) :
    Θ (MvPolynomial.X 0 * lin (fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb ![fnB v hv hc, N] n) D v := by
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => Pi.single (j.elim 0 id) 1
  have h := ((H.arIso k X p D hX).2 _ _ Θ hΘ).2.2 (Option (Fin 2))
    (fun o => o.elim (fnB v hv hc) ![fnB v hv hc, N]) A (by
      rintro (_ | i)
      · exact isometric_comb_single _ 0
      · exact isometric_comb_single _ i)
  have e (j : Option (Fin 2)) : (lin fun i => (A j i : ℝ)) = MvPolynomial.X (j.elim 0 id) := lin_single _
  rw [← H.arChange k X p D hX _ _ v hv hc _ h n, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  simp only [Function.comp_def, e, Option.elim_none, Option.elim_some, id, aeval_X_left_apply]

end GlobalTheory.SelfCont

end
end
