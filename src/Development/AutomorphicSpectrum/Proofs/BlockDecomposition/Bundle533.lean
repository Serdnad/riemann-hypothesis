module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellVal

section Blocks

variable {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n)

theorem block_mul₂ (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  simp only [bl]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem det_bl_unip (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem trace_bl_last (b : Matrix (Fin t) (Fin t) R) (Z : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (bl hn 0 0 0 b * Z) =
      Matrix.trace (b * Z.submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
        (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)) := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  have h1 : Z = (Matrix.fromBlocks (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  conv_lhs => rw [h1]
  simp only [bl, ← he]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun s => Matrix.fromBlocks _ _ _ _ s s), Fintype.sum_sum_type]
  simp

end Blocks

section Frames

variable {D : D7} {a n r t : ℕ} (hn : r + t = n)

theorem jn_mul_unip (x : Mx D a r) (y : Mx D r t) :
    (HMul.hMul (jn hn x 0) (bl hn 1 y 0 1) : Mx D a n) = jn hn x (mm x y) := by
  simp only [jn, bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [mm]

theorem trace_inner_jn (V : HSp D) (b : Mx D t t) (x : Mx D V.rank r) (v : Mx D V.rank t) :
    Matrix.trace (HMul.hMul (bl hn 0 0 0 b) (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)) : Mx D n n) =
      Matrix.trace (mm b (ip V v v)) := by
  rw [trace_bl_last]
  congr 1
  have h : (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)).submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
      (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr) = ip V v v := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, ip, mm, jn, adj, Matrix.mul_apply]
  rw [h]

def unipGL (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn
  inv_val := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn

theorem det_unipGL (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (unipGL hn y : GL (Fin n) (AE D)) = (1 : (AE D)ˣ) :=
  Units.ext (det_bl_unip hn y)

theorem adj_bl_unip_neg (y : Mx D r t) :
    adj (bl hn (1 : Mx D r r) (-y) 0 (1 : Mx D t t)) = bl hn (1 : Mx D r r) 0 (-adj y) (1 : Mx D t t) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [adj, bl, Matrix.one_apply, apply_ite (cA D)]
  all_goals by_cases h : i = j <;> simp [h, eq_comm]

end Frames

theorem weil_translate_frame {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ)
    (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t)
    (x : Mx D V.rank r) :
    (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) =
      ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  have e1 : ω (M.sh y * M.emb (w * nb b) * 1) Φ = ω (M.sh y) (ω (M.emb w) (ω (M.emb (nb b)) Φ)) := by
    simp only [mul_one, map_mul, Module.End.mul_apply]
  have hdet := det_unipGL hn y
  have hsh : mat (M.sh y) = blk4 (unipGL hn y).1 0 0 (adj ((unipGL hn y)⁻¹).1) := by
    rw [M.sh_mat]
    have : ((unipGL hn y)⁻¹).1 = bl hn 1 (-y) 0 1 := rfl
    rw [this, adj_bl_unip_neg]
    rfl
  have hemb : mat (M.emb (nb b)) = blk4 1 (bl hn 0 0 0 b.1) 0 1 := by
    rw [M.emb_mat (nb b) 1 b.1 0 1 (hnb b), blockRowSubstitution_one, blockMatrix_zero]
  rw [e1, hω.levi (M.sh y) (unipGL hn y) hsh, hdet]
  have hpow : npow (absA D 1) ((V.rank : ℂ) / 2) = 1 := by simp [npow]
  rw [map_one, hpow]
  simp only [Circle.coe_one, one_mul]
  have hj : (HMul.hMul (jn hn x 0) (unipGL hn y).1 : Mx D V.rank n) = jn hn x (mm x y) := jn_mul_unip hn x y
  rw [hj, (hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt (ω (M.emb (nb b)) Φ)).2.2 w hw x (mm x y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [hω.unip (M.emb (nb b)) _ hemb, trace_inner_jn]
  rfl

end GlobalTheory.CompanionTheory.CellVal

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AdeleComp

open TensorProduct

theorem coord_zero {F A B E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (ℬ : Module.Basis ι F E) (f : A →ₗ[F] B) (c : ι →₀ A)
    (h : LinearMap.rTensor E f (c.sum fun i m => m ⊗ₜ[F] ℬ i) = 0) (i : ι) : f (c i) = 0 := by
  have h1 : (c.mapRange f (map_zero f)).sum (fun i m => m ⊗ₜ[F] ℬ i) = 0 := by
    rw [Finsupp.sum_mapRange_index (by intro i; simp)]

    rw [← h, Finsupp.sum, Finsupp.sum, map_sum]
    simp
  have h2 := TensorProduct.sum_tmul_basis_right_eq_zero ℬ _ h1
  simpa using DFunLike.congr_fun h2 i

theorem adele_eq_zero {F : Type} [Field F] [NumberField F] (x : AF F)
    (hi : ∀ w, evInf F w x = 0) (hf : ∀ v, evFin F v x = 0) : x = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact RestrictedProduct.ext _ _ fun v => hf v

theorem tensor_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (a : AF F ⊗[F] E) (hi : ∀ w, compInf F E w a = 0) (hf : ∀ v, compFin F E v a = 0) : a = 0 := by
  let ℬ := Module.Basis.ofVectorSpace F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ a
  have hc : c = 0 := by
    ext i
    refine adele_eq_zero _ (fun w => ?_) (fun v => ?_)
    · refine coord_zero ℬ (evInf F w).toLinearMap c ?_ i
      rw [← hi w]

      simp only [compInf, Finsupp.sum, map_sum]
      rfl
    · refine coord_zero ℬ (evFin F v).toLinearMap c ?_ i
      rw [← hf v]

      simp only [compFin, Finsupp.sum, map_sum]
      rfl
  simp [hc]

theorem eq_zero_of_comps (D : D7) (a : AE D) (hi : ∀ w, compInf D.host.F D.host.E w a = 0)
    (hf : ∀ v, cv D v a = 0) : a = 0 :=
  tensor_eq_zero a hi hf

end GlobalTheory.CompanionTheory.AdeleComp
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WittS

section Abstract

variable {A B : Type} [CommRing A] [CommRing B]

theorem map_mul_of_mul (Q : B →+ A) (hQ : ∀ y y', Q (y * y') = Q y * Q y')
    {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B) :
    (X * Y).map Q = X.map Q * Y.map Q := by
  ext i j

  simp [Matrix.mul_apply, map_sum, hQ]

theorem exists_lift {m : Type} [Fintype m] [DecidableEq m] (c : A →+* A) (s : B →+* B) (P : A →+* B)
    (Q : B →+ A) (e : A) (hQs : ∀ y, Q (s y) = c (Q y)) (hQP : ∀ x, Q (P x) = e * x)
    (hQ : ∀ y y', Q (y * y') = Q y * Q y') (J : Matrix m m A) (g g' : Matrix m m B)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hU : (g.map s)ᵀ * J.map P * g = J.map P) :
    ∃ h h' : Matrix m m A, h * h' = 1 ∧ h' * h = 1 ∧ (h.map c)ᵀ * J * h = J ∧
      e • (h - 1) = h - 1 ∧
      ∀ (ι : Type) (N N' : Matrix m ι A), e • N = N → e • N' = N' → g * N.map P = N'.map P →
        h * N = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hQe : ∀ y, e * Q y = Q y := fun y => by rw [← hQ1, ← hQ, one_mul]
  have hee : e * e = e := by simpa [hQ1] using hQe 1
  have hce : c e = e := by rw [← hQ1, ← hQs, map_one]
  have hGe : ∀ {a b : Type} (X : Matrix a b B), e • X.map Q = X.map Q := by
    intro a b X
    ext i j
    simp [hQe]
  have hfz : ∀ {a b : Type} (X : Matrix a b B), (1 - e) • X.map Q = 0 := by
    intro a b X
    rw [sub_smul, one_smul, hGe, sub_self]
  have h1Q : (1 : Matrix m m B).map Q = e • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hQ1]
    · simp [Matrix.one_apply_ne hij]
  have hPQ : ∀ {a b : Type} (X : Matrix a b A), (X.map P).map Q = e • X := by
    intro a b X
    ext i j
    simp [hQP]
  have hfe : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hef : e * (1 - e) = 0 := by linear_combination -hee
  have hsum : ∀ {a b : Type} (X : Matrix a b A), e • X + (1 - e) • X = X := by
    intro a b X
    rw [← add_smul]
    simp
  have hmul : ∀ {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B),
      (X * Y).map Q = X.map Q * Y.map Q := fun X Y => map_mul_of_mul Q hQ X Y
  have hinv : ∀ u v : Matrix m m B, u * v = 1 →
      (u.map Q + (1 - e) • 1) * (v.map Q + (1 - e) • 1) = 1 := by
    intro u v huv
    rw [add_mul, mul_add, mul_add, ← hmul, huv, h1Q]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hfz, smul_smul, hfe, add_zero,
      zero_add]
    exact hsum 1
  have hstar : ((g.map Q + (1 - e) • (1 : Matrix m m A)).map c)ᵀ =
      ((g.map s)ᵀ).map Q + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hQs, hce]
    · simp [hQs, hce, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  refine ⟨g.map Q + (1 - e) • 1, g'.map Q + (1 - e) • 1, hinv _ _ hgg', hinv _ _ hg'g, ?_, ?_, ?_⟩
  · rw [hstar]
    have hJ : ((g.map s)ᵀ).map Q * J * g.map Q = e • J := by
      have h0 : ((g.map s)ᵀ).map Q * (e • J) = ((g.map s)ᵀ).map Q * J := by
        rw [mul_smul_comm, ← smul_mul_assoc, hGe]
      rw [← h0, ← hPQ J, ← hmul, ← hmul, hU]
    have hL : (1 - e) • (((g.map s)ᵀ).map Q * J) = 0 := by
      rw [← smul_mul_assoc, hfz, zero_mul]
    have hR : (1 - e) • (J * g.map Q) = 0 := by
      rw [← mul_smul_comm, hfz, mul_zero]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hJ, hL, hR,
      smul_smul, hfe, add_zero, zero_add]
    exact hsum J
  · have h1 : g.map Q + (1 - e) • (1 : Matrix m m A) - 1 = g.map Q - e • 1 := by
      rw [sub_smul, one_smul]
      abel
    rw [h1, smul_sub, hGe, smul_smul, hee]
  · intro ι N N' hN hN' hg
    have hz : (1 - e) • N = 0 := by
      rw [sub_smul, one_smul, hN, sub_self]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hz, add_zero]
    have h2 : g.map Q * N = g.map Q * (e • N) := by rw [hN]
    rw [h2, ← hPQ N, ← hmul, hg, hPQ, hN']

end Abstract

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_HR_of_gram (σ : E →ₐ[F] E) (hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (Ad : Type) [CommRing Ad] [Algebra F Ad] (R : Type) [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R] (e : Ad ⊗[F] E)
    (P : Ad ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ Ad ⊗[F] E)
    (hPinc : ∀ x, P (inclR Ad x) = inclR R x)
    (hPc : ∀ x, P (sigR Ad σ x) = sigR R σ (P x))
    (hQs : ∀ y, Q (sigR R σ y) = sigR Ad σ (Q y)) (hPQ : ∀ y, P (Q y) = y)
    (hQP : ∀ x, Q (P x) = e * x) (hQm : ∀ y y', Q (y * y') = Q y * Q y')
    (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι E) (hΓ : Γ.det ≠ 0)
    (N N' : Matrix (Fin M) ι (Ad ⊗[F] E)) (hN : e • N = N) (hN' : e • N' = N')
    (hG : (HMul.hMul (N.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad))
    (hG' : (HMul.hMul (N'.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N' : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad)) :
    ∃ h : HR Ad σ J, e • ((h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1) =
        (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1 ∧
      (HMul.hMul (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hPe : P e = 1 := by rw [← hQ1, hPQ]
  let eqv := Fintype.equivFin ι
  have gramX : ∀ N₀ : Matrix (Fin M) ι (Ad ⊗[F] E),
      (HMul.hMul (N₀.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N₀ : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad) →
      gramR R σ J (fun a i => P (N₀ i (eqv.symm a))) =
        (Γ.submatrix eqv.symm eqv.symm).map (inclR R) := by
    intro N₀ h₀
    ext a b
    have h := congrArg (fun X : Matrix ι ι (Ad ⊗[F] E) => P (X (eqv.symm a) (eqv.symm b))) h₀

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, hPc, hPe, one_mul, hPinc, Finset.mul_sum] at h
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.submatrix_apply, mul_assoc]
    exact h
  have hXY := (gramX N hG).trans (gramX N' hG').symm
  have hdet : IsUnit (gramR R σ J (fun a i => P (N i (eqv.symm a)))).det := by
    rw [gramX N hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_ne_zero.mpr hΓ).map _
  obtain ⟨hU, hact⟩ := GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM M J hJ R _ _ _
    hXY hdet
  let g : GL (Fin M) (R ⊗[F] E) := HeckeCharacterZeroLocus.SiegelWeilU.HA.mat R σ J hU
  have hJP : (J.map (inclR Ad)).map P = J.map (inclR R) := by
    ext i j
    simp [hPinc]
  have hmem : ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ *
      (J.map (inclR Ad)).map P * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J.map (inclR Ad)).map P := by
    rw [hJP]
    let h' : HeckeCharacterZeroLocus.SiegelWeilU.HR R σ J := hU
    exact h'.2
  have hgN : (HMul.hMul (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (N.map P) : Matrix (Fin M) ι (R ⊗[F] E)) = N'.map P := by
    ext i k
    have := congrFun (congrFun hact (eqv k)) i
    simpa [GlobalTheory.CompanionTheory.SW.actW, HeckeCharacterZeroLocus.SiegelWeilU.actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply, g]
      using this
  obtain ⟨h, h', h1, h2, h3, h4, h5⟩ := exists_lift (sigR Ad σ) (sigR R σ) P Q e hQs hQP hQm
    (J.map (inclR Ad)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (by simp) (by simp) hmem
  let u : GL (Fin M) (Ad ⊗[F] E) := ⟨h, h', h1, h2⟩
  have hu : u ∈ HR Ad σ J := h3
  exact ⟨⟨u, hu⟩, h4, h5 ι N N' hN hN' hgN⟩

end General

theorem exists_unitary_off_S : (∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R) (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D), (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧ (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧ ∀ y y', Q (y * y') = Q y * Q y') → ∀ (D : D7) (V : HSp D) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι D.host.E), Γ.det ≠ 0 → ∀ N N' : Matrix (Fin V.rank) ι (AE D), e • N = N → e • N' = N' → (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → (HMul.hMul (N'.map (cA D))ᵀ (HMul.hMul (gA V) N' : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → ∃ h : GA D V, e • (mt V h - 1) = mt V h - 1 ∧ (HMul.hMul (mt V h) N : Matrix (Fin V.rank) ι (AE D)) = N' := by
  intro H D V S e he ι _ _ Γ hΓ N N' hN hN' hG hG'
  obtain ⟨R, _, _, _, _, P, Q, hPinc, hPc, hQs, hPQ, hQP, hQm⟩ := H D S e he
  obtain ⟨h, h1, h2⟩ := exists_mem_HR_of_gram D.sp.cm.sig (isCMExt_host D) V.gram (isHermND_gram V)
    (AF D.host.F) R e P Q hPinc hPc hQs hPQ hQP hQm ι Γ hΓ N N' hN hN' hG hG'
  exact ⟨h, h1, h2⟩

end GlobalTheory.CompanionTheory.WittS
end
end

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr

theorem exists_frame_leftInv {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (P : Fx A r a) (M : Fx A t a) (hx : e • x = x) (hv : e • v = v) (hP : P * x = e • (1 : Fx A r r))
    (hM : M * (v - x * (P * v)) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have h2x : M * (1 - x * P) * x = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hP, Matrix.mul_smul,
      Matrix.mul_one, hx, sub_self, Matrix.mul_zero]
  have h2v : M * (1 - x * P) * v = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hM]
  have hPv : e • (P * v) = P * v := by
    rw [← Matrix.mul_smul, hv]
  refine ⟨P - (P * v) * (M * (1 - x * P)), M * (1 - x * P), ?_, ?_, h2x, h2v⟩
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2x, Matrix.mul_zero, sub_zero, hP]
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2v, Matrix.mul_smul, Matrix.mul_one, hPv, sub_self]

theorem exists_frame_leftInv_gram {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (B' B : Fx A r r) (C : Fx A r a) (H : Fx A a a) (M : Fx A t a) (hB : B' * B = 1)
    (hx : e • x = x) (hv : e • v = v) (hg : C * (H * x) = e • B)
    (hM : M * (v - x * (B' * (C * (H * v)))) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have hP : B' * (C * H) * x = e • (1 : Fx A r r) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_smul, hB]
  have hM' : M * (v - x * (B' * (C * H) * v)) = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc B', Matrix.mul_assoc C]
    exact hM
  exact exists_frame_leftInv e x v (B' * (C * H)) M hx hv hP hM'

theorem free_of_leftInv_orth {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D)
    (z : Mx D V.rank r × Mx D V.rank t) (hx : e • z.1 = z.1) (hv : e • z.2 = z.2)
    (hg : ip V z.1 z.1 = e • rat b₀.1)
    (M : Mx D t V.rank) (hM : mm M (z.2 - mm z.1 (yv V b₀ z)) = e • (1 : Mx D t t)) : Free e z := by
  have hB : rat b₀.1⁻¹ * rat b₀.1 = (1 : Mx D r r) := by
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hb
    simp only [rat]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  exact exists_frame_leftInv_gram e z.1 z.2 (rat b₀.1⁻¹) (rat b₀.1) (adj z.1) (gA V) M hB hx hv hg hM

end GlobalTheory.CompanionTheory.NullFr
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.section_left_invariant_rational_parabolic : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  first | exact @GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | exact GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | (intros; apply GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eisenstein_family_height_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | exact GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | (intros; apply GlobalTheory.CompanionTheory.FamMajorant.fam_majorant <;> assumption)
end
