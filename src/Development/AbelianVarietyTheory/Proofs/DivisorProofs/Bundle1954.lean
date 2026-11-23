module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducible
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomRowTransportContragredient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct
open Matrix
open Formalism.UG (cT)

namespace GlobalTheory.BlockFormsEmb

section Alg
variable {R : Type} [CommRing R] {n d : ℕ}

theorem cT_add' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A + B) = cT s A + cT s B :=
  Matrix.ext fun i j => by simp [cT]

theorem cT_sub' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A - B) = cT s A - cT s B :=
  Matrix.ext fun i j => by simp [cT]

def blk (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) R := 1 + a * (H - 1) * α + b * (K - 1) * β

variable {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}

theorem blk_one : blk a b α β 1 1 = 1 := by simp [blk]

theorem blk_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (H K H' K' : Matrix (Fin d) (Fin d) R) :
    blk a b α β H K * blk a b α β H' K' = blk a b α β (H * H') (K * K') := by
  first
  | exact @_root_.GlobalTheory.SquareDistanceExpansion.main
  | exact _root_.GlobalTheory.SquareDistanceExpansion.main
  | (apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareDistanceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareDistanceExpansion.main ..)

theorem blk_unitary (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R)
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT s α = Jm * b) (hβ : cT s β = Jm * a) (ha : cT s a * Jm = β) (hb : cT s b * Jm = α)
    (H K : Matrix (Fin d) (Fin d) R) (h1 : cT s K * H = 1) (h2 : cT s H * K = 1) :
    cT s (blk a b α β H K) * Jm * blk a b α β H K = Jm := by
  have key : cT s (blk a b α β H K) * Jm = Jm * blk a b α β (cT s K) (cT s H) := by
    unfold blk
    rw [cT_add', cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_sub', cT_sub',
      Formalism.UG.cT_one, hα, hβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, ha, hb]
    abel
  rw [key, Matrix.mul_assoc, blk_mul hαa hβb hαb hβa, h1, h2, blk_one, Matrix.mul_one]

end Alg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.BlockForms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem cT_adMat (σ : E →ₐ[F] E) {m p : Type} (Z : Matrix m p E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
  Matrix.ext fun i j => by simp only [cT, adMat, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]; rfl

theorem adMat_mul' {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {m : Type} [Fintype m] [DecidableEq m] : adMat F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {m p : Type} : adMat F (0 : Matrix m p E) = 0 := Matrix.map_zero _ (map_zero _)

theorem sigR_sigR' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem blkCols_gram {n r l d : ℕ} (h : l + d ≤ r) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (Z W : Matrix (Fin n) (Fin r) E) :
    cT (σ : E →+* E) (blkCols h Z) * J * blkCols h W =
      (cT (σ : E →+* E) Z * J * W).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
        (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := by
  first
  | rfl
  | (ext i j; simp [Matrix.mul_apply, blkCols, cT])

def embMat (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
    (a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E))
    (g : GlobalTheory.CuspRep.GA E d) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  blk a b α β (g.1.map Φ.symm) (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm))

variable (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
  {a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)} {α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E)}

theorem map_symm_mul (A B : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)) :
    (A * B).map Φ.symm = A.map Φ.symm * B.map Φ.symm := Matrix.map_mul (f := Φ.symm.toRingHom)

theorem map_symm_one : (1 : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)).map Φ.symm = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem embMat_one : embMat σ Φ a b α β 1 = 1 := by
  simp only [embMat, inv_one, Units.val_one, map_symm_one, Formalism.UG.cT_one, blk_one]

theorem embMat_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (g g' : GlobalTheory.CuspRep.GA E d) : embMat σ Φ a b α β (g * g') = embMat σ Φ a b α β g * embMat σ Φ a b α β g' := by
  unfold embMat
  rw [blk_mul hαa hβb hαb hβa, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_symm_mul, map_symm_mul, Formalism.UG.cT_mul]

theorem embMat_unitary (hσ : ∀ x, σ (σ x) = x) (Jm : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT (sigR (AF F) σ) α = Jm * b) (hβ : cT (sigR (AF F) σ) β = Jm * a)
    (ha : cT (sigR (AF F) σ) a * Jm = β) (hb : cT (sigR (AF F) σ) b * Jm = α) (g : GlobalTheory.CuspRep.GA E d) :
    cT (sigR (AF F) σ) (embMat σ Φ a b α β g) * Jm * embMat σ Φ a b α β g = Jm := by
  have hcc : ∀ A : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), cT (sigR (AF F) σ) (cT (sigR (AF F) σ) A) = A :=
    fun A => Matrix.ext fun i j => by simp only [cT, Matrix.transpose_apply, Matrix.map_apply]; exact sigR_sigR' σ hσ _
  have hgg : (g⁻¹).1.map Φ.symm * g.1.map Φ.symm = 1 := by
    rw [← map_symm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_symm_one]
  unfold embMat
  refine blk_unitary _ Jm hαa hβb hαb hβa hα hβ ha hb _ _ ?_ ?_
  · rw [hcc, hgg]
  · rw [← Formalism.UG.cT_mul, hgg, Formalism.UG.cT_one]

end Main

theorem exists_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (l d : ℕ) (h : l + d ≤ r), ∃ ι : GlobalTheory.CuspRep.GA E d →* GAd σ J, GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW l d h
  obtain ⟨Φ, j, hc1, hc2, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJT : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : ∀ {m p : Type} (Z : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun _ _ => hσ _
  have hyx : cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, hJT, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have he : Function.Injective (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := fun i k e =>
    Fin.ext (by have := congrArg Fin.val e; simp only at this; omega)
  have q1 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Xf = 1 := by
    rw [blkCols_gram, hyx, Matrix.submatrix_one _ he]
  have q2 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Yf = 1 := by
    rw [blkCols_gram, hW.xy, Matrix.submatrix_one _ he]
  have q3 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Yf = 0 := by
    rw [blkCols_gram, hW.yy, Matrix.submatrix_zero]; rfl
  have q4 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Xf = 0 := by
    rw [blkCols_gram, hW.xx, Matrix.submatrix_zero]; rfl
  have hαa : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Xf) = 1 := by
    rw [← adMat_mul', q1, adMat_one']
  have hβb : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Yf) = 1 := by
    rw [← adMat_mul', q2, adMat_one']
  have hαb : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Yf) = 0 := by
    rw [← adMat_mul', q3, adMat_zero']
  have hβa : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Xf) = 0 := by
    rw [← adMat_mul', q4, adMat_zero']
  have hα : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) = adMat F J * adMat F (blkCols h Yf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have hβ : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)) = adMat F J * adMat F (blkCols h Xf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have ha : cT (sigR (AF F) σ) (adMat F (blkCols h Xf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  have hb : cT (sigR (AF F) σ) (adMat F (blkCols h Yf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  let M := embMat σ Φ (adMat F (blkCols h Xf)) (adMat F (blkCols h Yf))
    (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J))
  have hMmul : ∀ g g', M (g * g') = M g * M g' := embMat_mul σ Φ hαa hβb hαb hβa
  have hMone : M 1 = 1 := embMat_one σ Φ
  have hMu : ∀ g, cT (sigR (AF F) σ) (M g) * JR (AF F) J * M g = JR (AF F) J :=
    embMat_unitary σ Φ hσ (adMat F J) hαa hβb hαb hβa hα hβ ha hb
  let U : GlobalTheory.CuspRep.GA E d → GL (Fin n) (AF F ⊗[F] E) := fun g =>
    ⟨M g, M g⁻¹, by rw [← hMmul, mul_inv_cancel, hMone], by rw [← hMmul, inv_mul_cancel, hMone]⟩
  let ι : GlobalTheory.CuspRep.GA E d →* GAd σ J :=
    { toFun := fun g => (⟨U g, hMu g⟩ : HR (AF F) σ J)
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun g g' => Subtype.ext (Units.ext (hMmul g g')) }
  exact ⟨ι, Φ, j, hc1, hc2, hj, hΦ, fun g => rfl⟩

end GlobalTheory.BlockFormsEmb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslInv

theorem translSnd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A,
    (∃ t : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) →
    LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h0 h1 h hh
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA L hL (G2 A) (lift (1 : G2 A ⟶ A) (snd A A))
    (toUnit _ ≫ lift 1 h) (lift (fst A A) 1)
  have zero_of : ∀ {Y : Scheme.{0}} (ψ : Y ⟶ (G2 A).left), (∃ t : (L.pull ψ).Gen, t.IsGen) →
      GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls L hL) = 0 := fun ψ hψ =>
    (GlobalTheory.CechPic.cls_pull hL ψ (pull_isLB hL ψ)).symm.trans ((GlobalTheory.CechPic.cls_eq_zero_iff _).2 hψ)
  have e_abc : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 =
      GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have e_ab : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) =
      (snd A A * (toUnit _ ≫ h)) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_ac : lift (1 : G2 A ⟶ A) (snd A A) * lift (fst A A) 1 = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_bc : (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 = fst A A ≫ lift (𝟙 A) (toUnit A ≫ h) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_a : lift (1 : G2 A ⟶ A) (snd A A) = snd A A ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_b : (toUnit _ ≫ lift 1 h : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_c : lift (fst A A) (1 : G2 A ⟶ A) = fst A A ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_1 : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  obtain ⟨t, ht⟩ := cube
  have hz := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb hL] at hz
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at hz
  rw [e_abc, e_ab, e_ac, e_bc, e_a, e_b, e_c, e_1] at hz
  simp only [Over.comp_left, Over.id_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_id,
    zero_of _ h0, zero_of _ h1, zero_of _ hh, map_zero] at hz
  simp only [one_zsmul, neg_one_zsmul, neg_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hL _)).1
    ((GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)).trans hz).symm

end GlobalTheory.TranslInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_detCharInvariant_same_value_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  first | exact @GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | exact GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | (intros; apply GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  first | exact @GlobalTheory.MinorFrame.exists_unitary_detChar_ne | exact GlobalTheory.MinorFrame.exists_unitary_detChar_ne | (intros; apply GlobalTheory.MinorFrame.exists_unitary_detChar_ne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  first | exact @GlobalTheory.MinorFrame.RowIrr.inv_irreducible | exact GlobalTheory.MinorFrame.RowIrr.inv_irreducible | (intros; apply GlobalTheory.MinorFrame.RowIrr.inv_irreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  first | exact @GlobalTheory.LieInt.colSub_unitary_of_coinv | exact GlobalTheory.LieInt.colSub_unitary_of_coinv | (intros; apply GlobalTheory.LieInt.colSub_unitary_of_coinv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.definite_bottom_row_transport_contragredient : ∀ (D : D7) (M M' X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (A' : GlobalTheory.ChainFr.Fr M') (B : GlobalTheory.ChainFr.Fr X)
    (eS eS' : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : PolF D X.rank M.rank →ₗ[ℂ] Q) (q' : PolF D X.rank M'.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ j, A'.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = eS τ - eS' τ - ((M.rank : ℚ) + (M'.rank : ℚ)) / 2) →
    (∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt X τ,
      q (GlobalTheory.RealQuot.actT true A B eS τ Y P) = q' (GlobalTheory.RealQuot.actT false A' B eS' τ Y P')) →
    ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin X.rank) ℂ) (P : PolF D X.rank M.rank) (P' : PolF D X.rank M'.rank), q P = q' P' →
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) P') =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) •
          q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.RowTransport.row_transport | exact GlobalTheory.RowTransport.row_transport | (intros; apply GlobalTheory.RowTransport.row_transport <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def iotaW (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.InertLocField.liftT (E := E) v).toAddMonoidHom.comp
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom.toAddMonoidHom

def conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+* w.adicCompletion E :=
  (toCompl (under_eq_of_isInertAt hw)).comp
    ((sigR (Fv F v) σ).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom)

def glueW (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + P.map (iotaW hw)

def InLat {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (u : Fin d → K) : Prop :=
  ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u) i ∈ O

def InLat2 {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (z : Fin d ⊕ Fin d → K) : Prop :=
  InLat O b (z ∘ Sum.inl) ∧ InLat O b (z ∘ Sum.inr)

end GlobalTheory.InertBigCell
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.heckeCharacter_unramified_inert_kills_units : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  first | exact @GlobalTheory.UnrKill.unr_kill | exact GlobalTheory.UnrKill.unr_kill | (intros; apply GlobalTheory.UnrKill.unr_kill <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.heckeCharacter_trivial_subfield_kills_idele_norms : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.NuCharNorm.chi_norm_one | exact GlobalTheory.NuCharNorm.chi_norm_one | (intros; apply GlobalTheory.NuCharNorm.chi_norm_one <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  first | exact @GlobalTheory.HeckeCont.eq_one_of_cong | exact GlobalTheory.HeckeCont.eq_one_of_cong | (intros; apply GlobalTheory.HeckeCont.eq_one_of_cong <;> assumption)
end
