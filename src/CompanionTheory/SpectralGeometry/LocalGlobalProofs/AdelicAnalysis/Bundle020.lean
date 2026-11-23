module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealCoord

open InfinitePlace InfinitePlace.Completion

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def rho (w : InfinitePlace F) : F →+* ℝ := embedding_of_isReal (IsTotallyReal.isReal w)

def coord : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight (R := fun w : InfinitePlace F => w.Completion) (S := fun _ => ℝ)
    (fun w => ringEquivRealOfIsReal (IsTotallyReal.isReal w))

theorem coord_apply (y : Ainf F) (w : InfinitePlace F) :
    coord F y w = ringEquivRealOfIsReal (IsTotallyReal.isReal w) (y w) := rfl

def coordHomeo : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight (Y₁ := fun w : InfinitePlace F => w.Completion) (Y₂ := fun _ => ℝ)
    (fun w => (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).toHomeomorph)

theorem coordHomeo_coe : ⇑(coordHomeo F) = ⇑(coord F) := rfl

theorem isHomeomorph_coord : IsHomeomorph (coord F) := (coordHomeo F).isHomeomorph

theorem abs_coord (y : Ainf F) (w : InfinitePlace F) : |coord F y w| = ‖y w‖ := by
  have h := (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry.norm_map_of_map_zero
    (map_zero (ringEquivRealOfIsReal (IsTotallyReal.isReal w))) (y w)
  exact h

theorem rho_coe (w : InfinitePlace F) (x : F) : ((rho F w x : ℝ) : ℂ) = w.embedding x :=
  embedding_of_isReal_apply _ _

theorem coord_algebraMap (x : F) (w : InfinitePlace F) :
    coord F (algebraMap F (Ainf F) x) w = rho F w x := by
  have h : ((coord F (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = ((rho F w x : ℝ) : ℂ) := by
    rw [rho_coe, coord_apply, InfiniteAdeleRing.algebraMap_apply, ringEquivRealOfIsReal_apply,
      extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
  exact Complex.ofReal_injective h

instance : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => not_isReal_iff_isComplex.mpr w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed (y : InfinitePlace F → ℝ) : mixedEmbedding.mixedSpace F :=
  (fun w => y w.1, 0)

theorem toMixed_add (y z : InfinitePlace F → ℝ) : toMixed F (y + z) = toMixed F y + toMixed F z := by
  refine Prod.ext rfl ?_
  simp [toMixed]

theorem toMixed_injective : Function.Injective (toMixed F) := by
  intro y z h
  funext w
  exact congrFun (congrArg Prod.fst h) ⟨w, IsTotallyReal.isReal w⟩

theorem toMixed_coord_algebraMap (x : F) :
    toMixed F (coord F (algebraMap F (Ainf F) x)) = mixedEmbedding F x := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext w
  rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  exact coord_algebraMap F x w.1

open scoped Classical in
theorem measurePreserving_toMixed : MeasurePreserving (toMixed F) volume volume := by
  let f : {w : InfinitePlace F // w.IsReal} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv IsTotallyReal.isReal
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) f).symm
  have h2 : MeasurePreserving (fun y : InfinitePlace F → ℝ => fun w : {w : InfinitePlace F // w.IsReal} => y w.1)
      volume volume := by
    convert h1 using 1
    funext y w
    rfl
  refine ⟨?_, ?_⟩
  · exact h2.measurable.prodMk measurable_const
  · have hm : Measurable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ =>
        (x, (0 : {w : InfinitePlace F // w.IsComplex} → ℂ))) := by fun_prop
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ),
      Measure.pi_of_empty _ (0 : {w : InfinitePlace F // w.IsComplex} → ℂ), Measure.prod_dirac, ← h2.map_eq,
      Measure.map_map hm h2.measurable]
    rfl

theorem coord_measurable : Measurable (coord F) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact (isHomeomorph_coord F).continuous.measurable

open scoped Classical in
theorem map_coord_eq (lam : Measure (Ainf F)) (hl : IsStdInf lam) :
    lam.map (coord F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  obtain ⟨hH, D, hD, hD1⟩ := hl
  haveI := hH
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : (lam.map (coord F)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam (coord F).toAddEquiv (isHomeomorph_coord F).continuous
      (coordHomeo F).symm.continuous
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam.map (coord F) = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  set P := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) with hP
  have hmp := measurePreserving_toMixed F
  have hPm : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set Λ := mixedEmbedding.integerLattice F with hΛdef
  set Γ : AddSubgroup (Ainf F) :=
    ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range with hΓ
  let Ψ : Ainf F → mixedEmbedding.mixedSpace F := fun y => toMixed F (coord F y)
  have hΨadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => by
    simp only [Ψ, map_add (f := _), toMixed_add]
  have hΨinj : Function.Injective Ψ := (toMixed_injective F).comp (coord F).injective
  have hΨalg : ∀ a : 𝓞 F, Ψ (algebraMap F (Ainf F) (algebraMap (𝓞 F) F a)) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := fun a => toMixed_coord_algebraMap F _
  have hΛmem : ∀ g : Λ, ∃ a : 𝓞 F, (g : mixedEmbedding.mixedSpace F) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hΛmem' : ∀ a : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F a) ∈ Λ :=
    fun a => ⟨a, rfl⟩
  choose a ha using hΛmem
  let m : Λ → Γ := fun g => ⟨algebraMap F (Ainf F) (algebraMap (𝓞 F) F (a g)), ⟨a g, rfl⟩⟩
  have hmΨ : ∀ g : Λ, Ψ (m g : Ainf F) = g := fun g => by
    rw [ha g]; exact hΨalg _
  have hmbij : Function.Bijective m := by
    refine ⟨fun g g' h => ?_, ?_⟩
    · apply Subtype.ext
      rw [← hmΨ g, ← hmΨ g', h]
    · rintro ⟨_, b, rfl⟩
      refine ⟨⟨_, hΛmem' b⟩, Subtype.ext (hΨinj ?_)⟩
      rw [hmΨ]
      exact (hΨalg b).symm
  have hq : Measure.QuasiMeasurePreserving Ψ lam volume := by
    refine hmp.quasiMeasurePreserving.comp ⟨(coord_measurable F).aemeasurable, ?_⟩
    rw [hc]
    intro s hs
    simp [hs]
  have hFD : IsAddFundamentalDomain Γ (Ψ ⁻¹' P) lam :=
    (mixedEmbedding.fundamentalDomain_integerLattice F).preimage_of_equiv hq hmbij (fun g x => by
      change Ψ ((m g : Ainf F) + x) = (g : mixedEmbedding.mixedSpace F) + Ψ x
      rw [hΨadd, hmΨ])
  haveI : Countable Γ := hmbij.surjective.countable
  have h1 : lam (Ψ ⁻¹' P) = 1 := by
    rw [← hD1]
    exact hFD.measure_eq hD
  have hQm : MeasurableSet (toMixed F ⁻¹' P) := hmp.measurable hPm
  have h2 : (c : ℝ≥0∞) * volume (toMixed F ⁻¹' P) = 1 := by
    have := Measure.map_apply (μ := lam) (coord_measurable F) hQm
    rw [hc] at this
    have e : Ψ ⁻¹' P = coord F ⁻¹' (toMixed F ⁻¹' P) := rfl
    rw [← h1, e]
    simpa using this
  have h3 : volume (toMixed F ⁻¹' P) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [hmp.measure_preimage hPm.nullMeasurableSet, hP, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
      IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul,
      ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hd : 0 < Real.sqrt |(discr F : ℝ)| := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    positivity
  rw [h3] at h2
  have h4 : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hd]
    exact ENNReal.eq_inv_of_mul_eq_one_left h2
  rw [hc, ← h4]
  rfl

end GlobalTheory.CompanionTheory.SW.RealCoord

open GlobalTheory.CompanionTheory.SW.RealCoord in
theorem GlobalTheory.CompanionTheory.SW.real_iso : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  intro F _ _ hF
  haveI := hF
  exact ⟨rho F, coord F, rho_coe F, isHomeomorph_coord F, coord_algebraMap F, abs_coord F, map_coord_eq F⟩
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem quad_mulVec (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by
  rw [GlobalTheory.ofReal_mulVec_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => (v i : ℂ)) ((P.map Complex.ofReal)ᵀ), Matrix.vecMul_transpose]

theorem contragredient_congr {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) (Z : Matrix κ κ ℂ) :
    (((g⁻¹)ᵀ).map Complex.ofReal)ᵀ * Z⁻¹ * ((g⁻¹)ᵀ).map Complex.ofReal =
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹ := by
  have hC : (g⁻¹).map Complex.ofReal = (g.map Complex.ofReal)⁻¹ := (GlobalTheory.inv_map_ofReal hg).symm
  have hC' : ((g⁻¹)ᵀ).map Complex.ofReal = ((g.map Complex.ofReal)⁻¹)ᵀ := by
    rw [Matrix.transpose_map, hC]
  rw [hC', Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem gaussian_lattice_term (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0)
    (a : κ → ℝ) (n : κ → ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z *ᵥ fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n := by
  have hv : a + g *ᵥ (fun i => (n i : ℝ)) = g *ᵥ ((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg),
      Matrix.one_mulVec, add_comm]
  have hs : (fun i => ((((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) i : ℝ) : ℂ)) =
      ReciprocityTheory.PTheta.shiftVec (g⁻¹ *ᵥ a) n := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  rw [hv, quad_mulVec, hs]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero]
  congr 1
  ring

theorem gaussian_fourier {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) (y : κ → ℝ) :
    ∫ x : κ → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z * Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => (y i : ℂ)) ⬝ᵥ (Z⁻¹ *ᵥ fun i => (y i : ℂ)))) := by
  have hq := hZ.integral_cexp_quadratic (fun i => (y i : ℂ))
  rw [← hq]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  have hxy : ((x ⬝ᵥ y : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (y i : ℂ)) := by
    simp [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hxy]
  ring

theorem siegelGaussIntegral_congr (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) :
    GlobalTheory.siegelGaussIntegral ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) =
      ((|g.det|⁻¹ : ℝ) : ℂ) * GlobalTheory.siegelGaussIntegral Z := by
  have hv : Continuous fun y : κ → ℝ => fun i => (y i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hf : Continuous fun y : κ → ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (y i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (y i : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul (hv.dotProduct (continuous_const.matrix_mulVec hv)))
  have key := GlobalTheory.integral_comp_mulVec_of_det_ne_zero hg hf
  simp only [quad_mulVec] at key
  simp only [GlobalTheory.siegelGaussIntegral]
  rw [← abs_inv]
  exact key

theorem fourier_lattice_term {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) {g : Matrix κ κ ℝ}
    (hg : g.det ≠ 0) (n : κ → ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z⁻¹ *ᵥ fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  have hs : ReciprocityTheory.PTheta.shiftVec (0 : κ → ℝ) n = fun i => (((n i : ℝ)) : ℂ) := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  rw [quad_mulVec, contragredient_congr hg]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero, hs, Matrix.neg_mulVec, dotProduct_neg]
  congr 1
  ring

theorem phase_lattice {g : Matrix κ κ ℝ} (a : κ → ℝ) (n : κ → ℤ) :
    ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ) =
      (fun i => (n i : ℂ)) ⬝ᵥ fun i => ((g⁻¹ *ᵥ a) i : ℂ) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem poisson_shifted_lattice : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ | x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ | y => (∫ x,
      f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) = GlobalTheory.siegelGaussIntegral Z *
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) = GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def, ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0

end GlobalTheory.CompanionTheory.SW.Core.PoiLat
end
end
