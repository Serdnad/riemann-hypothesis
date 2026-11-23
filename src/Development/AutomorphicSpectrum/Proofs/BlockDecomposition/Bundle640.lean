module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdeles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := rfl

theorem hR_apply (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x y = ∑ i, ∑ j, sigR (Fv F v) σ (x i) * inclR (Fv F v) (J i j) * y j := rfl

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_hR (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  rw [hR_apply, hR_apply, Finset.sum_comm]

  simp only [map_sum, map_mul, sigR_sigR hσ, sigR_inclR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ i j]
  ring

theorem hR_mem (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ intLoc F E v) (hy : ∀ i, y i ∈ intLoc F E v) : hR (Fv F v) σ J x y ∈ intLoc F E v := by
  rw [hR_apply]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sigR_mem_intLoc σ (hx i)) (hJv i j)) (hy j)

theorem hR_single (i : Fin n) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (Pi.single i 1) z = (J.map (inclR (F := F) (Fv F v)) *ᵥ z) i := by
  rw [hR_apply, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem mem_of_hR_single (hdet : J.det ≠ 0) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : ∀ i, hR (Fv F v) σ J (Pi.single i 1) z ∈ intLoc F E v) (a : Fin n) :
    z a ∈ intLoc F E v := by
  have e : J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _) (map_one _)]
  have hz' : z = J⁻¹.map (inclR (F := F) (Fv F v)) *ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, w = J.map (inclR (F := F) (Fv F v)) *ᵥ z := ⟨_, rfl⟩
  have hw' : ∀ j, w j ∈ intLoc F E v := fun j => by rw [hw, ← hR_single (σ := σ)]; exact hz j
  rw [← hw] at hz'
  rw [hz']
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hJi a j) (hw' j)

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem single_mem_latLoc_std (i : Fin n) :
    (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E n) v := by
  refine mem_latLoc_stdLattice.2 fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem sum_single_smul (y : Fin n → Fv F v ⊗[F] E) : ∑ i, y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem isLat_latLoc_std : IsLat (intLoc F E v) (latLoc F (stdLattice E n) v) := by
  constructor
  · refine Submodule.fg_def.2 ⟨Set.range fun i => (Pi.single i 1 : Fin n → Fv F v ⊗[F] E), Set.finite_range _,
      le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact single_mem_latLoc_std i
    · intro y hy
      have h := mem_latLoc_stdLattice.1 hy
      rw [← sum_single_smul y]
      refine sum_mem fun i _ => ?_
      have : y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) =
          (⟨y i, h i⟩ : intLoc F E v) • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [eq_top_iff]
    intro y _
    rw [← sum_single_smul y]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_latLoc_std i))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem hR_self_eq (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x x = inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x +
      sigR (Fv F v) σ (inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x) := by
  have hs : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [map_mul, sigR_hR hσ hJ, sigR_inclR, hs, ← add_mul, ← map_add (f := _)]
  have : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [this, map_one, one_mul]

theorem isMaxEven_isAdapted_std (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    (h2 : inclR (Fv F v) (2⁻¹ : E) ∈ intLoc F E v) {r : ℕ} (x y : Fin r → Fin n → Fv F v ⊗[F] E)
    (hx : ∀ i a, x i a ∈ intLoc F E v) (hy : ∀ i a, y i a ∈ intLoc F E v) :
    IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F (stdLattice E n) v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) x y (latLoc F (stdLattice E n) v) := by
  have hint : ∀ a ∈ latLoc F (stdLattice E n) v, ∀ b ∈ latLoc F (stdLattice E n) v,
      hR (Fv F v) σ J a b ∈ intLoc F E v := fun a ha b hb =>
    hR_mem hJv (mem_latLoc_stdLattice.1 ha) (mem_latLoc_stdLattice.1 hb)
  refine ⟨⟨isLat_latLoc_std, ⟨hint, fun a ha => ⟨_, mul_mem h2 (hint a ha a ha), hR_self_eq hσ hJ.1 a⟩⟩, ?_⟩, ?_⟩
  · intro L' hL' hle z hz
    refine mem_latLoc_stdLattice.2 (mem_of_hR_single (σ := σ) hJ.2 hJi fun i => ?_)
    exact hL'.1 _ (hle (single_mem_latLoc_std i)) _ hz
  · intro z
    simp only [mem_latLoc_stdLattice]
    have hc : ∀ (c d : Fin r → Fv F v ⊗[F] E) (a : Fin n),
        (z - ∑ i, c i • x i - ∑ i, d i • y i) a = z a - ∑ i, c i * x i a - ∑ i, d i * y i a := by
      intro c d a
      simp [Finset.sum_apply]
    constructor
    · intro hz
      have h1 : ∀ i, hR (Fv F v) σ J (x i) z ∈ intLoc F E v := fun i => hR_mem hJv (hx i) hz
      have h3 : ∀ i, hR (Fv F v) σ J (y i) z ∈ intLoc F E v := fun i => hR_mem hJv (hy i) hz
      refine ⟨h1, h3, fun a => ?_⟩
      rw [hc]
      exact sub_mem (sub_mem (hz a) (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))
    · rintro ⟨h1, h3, hw⟩ a
      have := hw a
      rw [hc] at this
      have e : z a = (z a - ∑ i, hR (Fv F v) σ J (y i) z * x i a - ∑ i, hR (Fv F v) σ J (x i) z * y i a) +
          ∑ i, hR (Fv F v) σ J (y i) z * x i a + ∑ i, hR (Fv F v) σ J (x i) z * y i a := by ring
      rw [e]
      exact add_mem (add_mem this (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

theorem exists_lattice_maxEven_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ _hW
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  refine ⟨stdLattice E n, isLattice_stdLattice.toIsLattice, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
    eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
    with v h1 h2 h3 h4 h5
  exact isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5

end GlobalTheory.CompanionTheory.KFin.AE
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.FrameLoc

theorem hR_colV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (i j : Fin r) :
    hR (Fv F v) σ J (colV v X i) (colV v Y j) = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) X * J * Y) i j) := by
  have hs : ∀ t : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) t) = inclR (F := F) (Fv F v) (σ t) := by
    intro t; simp [sigR, inclR]

  simp only [hR, Formalism.UG.hform, colV, JR, Matrix.map_apply, hs, Matrix.mul_apply, cT, Matrix.transpose_apply,
  map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem isFrame_colV : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), IsFrame (hR (Fv F v) σ J) (colV v X) (colV v Y) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ hW v
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [hR_colV, hW.xx]; simp
  · rw [hR_colV, hW.yy]; simp
  · rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.CompanionTheory.KFin.FrameLoc
end

section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.GoodLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem sigR_inclR (A : Type) [CommRing A] [Algebra F A] (e : E) :
    sigR A σ (inclR (F := F) A e) = inclR (F := F) A (σ e) := by
  simp [sigR, inclR]

theorem dual_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) (i : Fin r) :
    ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) *ᵥ z) i
      = hR (Fv F v) σ J (colV v A i) z := by

  simp only [hR, Formalism.UG.hform, colV, JR, sigR_inclR, mulVec, dotProduct, map_apply, Matrix.mul_apply,
  cT, transpose_apply, map_sum, map_mul, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem col_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (w : Fin r → Fv F v ⊗[F] E) :
    A.map (inclR (F := F) (Fv F v)) *ᵥ w = ∑ i, w i • colV v A i := by
  ext a
  simp [mulVec, dotProduct, colV, Finset.sum_apply, mul_comm]

theorem hR_colV (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin r) E) (i j : Fin r) :
    hR (Fv F v) σ J (colV v A i) (colV v B j)
      = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) A * J * B) i j) := by
  rw [← dual_mulVec]
  conv_rhs => rw [Matrix.mul_apply]

  simp only [mulVec, dotProduct, map_apply, colV, map_sum, map_mul]

theorem sigma_sigma (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]

theorem cT_mul_rect (s : E →+* E) {a b c : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b c E) :
    cT s (P * Q) = cT s Q * cT s P := by
  simp [cT, Matrix.map_mul, transpose_mul]

theorem gram_yx (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 := by
  have hcT : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    exact sigma_sigma hCM _
  have h1 : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rw [cT_mul_rect, cT_mul_rect, hcT, hcc, h1, ← Matrix.mul_assoc] at this
  exact this

def projP (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  1 - X.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) Y * J).map (inclR (F := F) (Fv F v))
    - Y.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))

theorem projP_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) :
    projP v σ J X Y *ᵥ z = z - ∑ i, hR (Fv F v) σ J (colV v Y i) z • colV v X i
      - ∑ i, hR (Fv F v) σ J (colV v X i) z • colV v Y i := by
  have hb : ∀ A B : Matrix (Fin n) (Fin r) E,
      (A.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, hR (Fv F v) σ J (colV v B i) z • colV v A i := by
    intro A B
    rw [← mulVec_mulVec, col_mulVec]
    simp only [dual_mulVec]
  simp only [projP, sub_mulVec, one_mulVec, hb]

theorem leviMat_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (z : Fin n → Fv F v ⊗[F] E) :
    leviMat σ J (Fv F v) X Y M *ᵥ z =
      ∑ i, (hR (Fv F v) σ J (colV v Y i) (M *ᵥ colV v X i) * hR (Fv F v) σ J (colV v Y i) z) • colV v X i
      + ∑ i, (hR (Fv F v) σ J (colV v X i) (M *ᵥ colV v Y i) * hR (Fv F v) σ J (colV v X i) z) • colV v Y i
      + projP v σ J X Y *ᵥ (M *ᵥ (projP v σ J X Y *ᵥ z)) := by
  have hd : ∀ (A B : Matrix (Fin n) (Fin r) E) (i : Fin r),
      ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) * M * B.map (inclR (F := F) (Fv F v))) i i
        = hR (Fv F v) σ J (colV v A i) (M *ᵥ colV v B i) := by
    intro A B i
    rw [← dual_mulVec, Matrix.mul_assoc]
    rfl
  have hmv : ∀ (A B : Matrix (Fin n) (Fin r) E) (d : Fin r → Fv F v ⊗[F] E),
      (A.map (inclR (F := F) (Fv F v)) * diagonal d * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, (d i * hR (Fv F v) σ J (colV v B i) z) • colV v A i := by
    intro A B d
    rw [← mulVec_mulVec, ← mulVec_mulVec, col_mulVec]
    simp only [mulVec_diagonal, dual_mulVec]
  unfold leviMat
  simp only [add_mulVec]
  rw [hmv, hmv]
  simp only [hd]
  simp only [mulVec_mulVec, projP, Matrix.mul_assoc]

theorem hR_isom {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v) (a b : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J ((matHom _ σ J g).1 *ᵥ a) ((matHom _ σ J g).1 *ᵥ b) = hR (Fv F v) σ J a b := by
  have hg : cT (sigR (Fv F v) σ) (matHom _ σ J g).1 * JR (Fv F v) J * (matHom _ σ J g).1 = JR (Fv F v) J := g.2
  simp only [hR]
  rw [Formalism.UG.P.hform_mulVec, hg]

theorem levi_mem_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v Λ hΛ hA p m hp B _ _ hm
  obtain ⟨-, ⟨hint, heven⟩, hmax⟩ := hΛ
  have hxx : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v X j) = 0 := fun i j => by
    rw [hR_colV, hW.xx]; simp
  have hyy : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v Y j) = 0 := fun i j => by
    rw [hR_colV, hW.yy]; simp
  have hxy : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v Y j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  have hyx : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v X j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, gram_yx hCM hJ hW, Matrix.one_apply]; split_ifs <;> simp
  have hδ : ∀ i j : Fin r, ((if i = j then 1 else 0 : Fv F v ⊗[F] E)) ∈ intLoc F E v := fun i j => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hx : ∀ i, colV v X i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxx]; exact zero_mem _
    · rw [hyx]; exact hδ _ _
    · simp [hxx, hyx]
  have hy : ∀ i, colV v Y i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxy]; exact hδ _ _
    · rw [hyy]; exact zero_mem _
    · simp [hxy, hyy]
  have hP : ∀ z ∈ Λ, projP v σ J X Y *ᵥ z ∈ Λ := fun z hz => by
    rw [projP_mulVec]
    exact ((hA z).1 hz).2.2
  have hsm : ∀ a ∈ intLoc F E v, ∀ z ∈ Λ, a • z ∈ Λ := fun a ha z hz => Λ.smul_mem ⟨a, ha⟩ hz
  have hpz : ∀ z ∈ Λ, (matHom _ σ J p).1 *ᵥ z ∈ Λ := fun z hz => (hp z).1 hz
  have hsub : ∀ z ∈ Λ, (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z hz => by
    rw [hm, leviMat_mulVec]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) (sum_mem fun i _ => ?_)) (hP _ (hpz _ (hP z hz)))
    · exact hsm _ (mul_mem (hint _ (hy i) _ (hpz _ (hx i))) (hint _ (hy i) _ hz)) _ (hx i)
    · exact hsm _ (mul_mem (hint _ (hx i) _ (hpz _ (hy i))) (hint _ (hx i) _ hz)) _ (hy i)
  let L' : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := {z | (matHom _ σ J m).1 *ᵥ z ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, mulVec_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a z hz => by
        have e : (matHom _ σ J m).1 *ᵥ (a • z) = a • ((matHom _ σ J m).1 *ᵥ z) := by
          change (matHom _ σ J m).1 *ᵥ ((a : Fv F v ⊗[F] E) • z) = (a : Fv F v ⊗[F] E) • ((matHom _ σ J m).1 *ᵥ z)
          rw [mulVec_smul]
        change (matHom _ σ J m).1 *ᵥ (a • z) ∈ Λ
        rw [e]
        exact Λ.smul_mem a hz }
  have hL' : ∀ z, z ∈ L' ↔ (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z => Iff.rfl
  have hev : IsEvenInt (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) L' := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [← hR_isom m a b]
      exact hint _ ha _ hb
    · rw [← hR_isom m a a]
      exact heven _ ha
  have hle : L' ≤ Λ := hmax L' hev hsub
  exact fun y => ⟨hsub y, fun h => hle h⟩

end GlobalTheory.CompanionTheory.KFin.GoodLocal

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassHasse

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ _ hmi _ β hβ hne
  by_contra hS
  have hnot : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E β := fun x hx =>
    hS ⟨fun _ => x, by
      funext a c
      simpa [gramE] using hx⟩
  obtain ⟨τ, c, hc0, hc, hw⟩ := Plane.exists_place hCM J hJ β hβ hnot
  obtain ⟨Φ, hΦ, hΦσ⟩ := Plane.exists_hom hCM τ
  have hscal : algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) = inclR (Ainf F) (algebraMap F E β) := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hempty : (gramR (Ainf F) σ J ⁻¹' {(hermScal (Ainf F) σ (algebraMap F (Ainf F) β)).1} ∩
      {X | IsUnit (gramR (Ainf F) σ J X).det}) = ∅ := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hY _
    have h00 : hR (Ainf F) σ J (Y 0) (Y 0) = inclR (Ainf F) (algebraMap F E β) :=
      (congrFun (congrFun hY 0) 0).trans hscal
    have h1 := congrArg Φ h00
    rw [hΦ, hc] at h1
    let w : Fin 2 → ℂ := fun i => Φ (Y 0 i)
    have key : Φ (hR (Ainf F) σ J (Y 0) (Y 0)) = star w ⬝ᵥ (J.map τ *ᵥ w) := by

      simp only [hR, hform, JR, map_sum, map_mul, hΦσ, Matrix.map_apply, hΦ, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum, w, mul_assoc]
    have h2 := hw w
    rw [← key, h1, Complex.ofReal_re] at h2
    exact absurd (mul_self_pos.2 hc0) (not_lt.2 h2)
  apply hne
  have h1 := hmi.1 (hermScal (Ainf F) σ (algebraMap F (Ainf F) β))
  rw [hempty, Set.compl_empty] at h1
  exact Measure.measure_univ_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SW.MassHasse
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_selfdual_measure_hermitian_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ ν : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm | exact GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm | (intros; apply GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm <;> assumption)
end
