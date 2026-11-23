module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle553
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GaussThetaAlg

def transposeMulEquiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    (G H : Matrix β β A) (hHG : H * G = 1) : Matrix β γ A ≃+ Matrix α β A where
  toFun u := uᵀ.submatrix e.symm id * G
  invFun x := (x * H)ᵀ.submatrix id e
  left_inv u := by
    show ((uᵀ.submatrix e.symm id * G) * H)ᵀ.submatrix id e = u
    rw [Matrix.mul_assoc, mul_eq_one_comm.1 hHG, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    show ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id * G = x
    have : ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e.symm id * G = _
    rw [← Matrix.add_mul]
    rfl

theorem mem_algF_of_isFinF {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M)
    (B : Fr X) (f : WO M X → ℂ) (hf : IsFinF ψ θ ε A B f) : f ∈ algF ψ θ ε A B := by
  refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
  show f = pureTensorL _ f 1
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  simp only [pureTensorL]
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem isFinF_thO (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ) (hg : M.IsGauss Bs.ψ Bs.emb g)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) := by
  classical
  have hsg : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [sgn, HSpace.gram]
  have hdet : IsUnit ((if ε then -1 else 1 : D.host.E) • S.gram).det := by
    rw [Matrix.det_smul]
    refine IsUnit.mul (IsUnit.pow _ (by cases ε <;> simp)) ?_
    exact LatVac.gram_det_isUnit S
  have hHG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨f, hf, hD⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ
    (by rw [hJW]; rfl) hV hW (fun w => by
      obtain ⟨τ, h1, h2, h3⟩ := hemb w
      exact ⟨τ, h1, h2, by rw [h3]; rfl⟩) M hM
    (transposeMulEquiv e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹) hHG)
    (fun u => rfl) g φ hg hφ hvac
  convert hf using 1
  funext x
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn ε S).gram e x)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) = f x
  rw [hD.2, hsg]
  congr 1
  show (((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id) *
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = x
  have hx : ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id =
      x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ := by
    ext i j
    simp
  rw [hx, Matrix.mul_assoc, hHG, Matrix.mul_one]

end GlobalTheory.GaussThetaAlg

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrOff

theorem idem_apply_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (a : FiniteAdeleRing (𝓞 E) E) (ha : a * a = a)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 →
      ¬ ∀ Q, Valued.v ((a * algebraMap E (FiniteAdeleRing (𝓞 E) E) ((x : E)⁻¹)) Q) ≤ 1) : a P = 1 := by
  have h01 : ∀ Q, a Q ≠ 0 → a Q = 1 := fun Q hQ =>
    mul_left_cancel₀ hQ (by rw [← GlobalTheory.PlaceIdem.mul_ap, ha, mul_one])
  refine h01 P fun h0 => ?_
  obtain ⟨n, hn, x, hx⟩ := GlobalTheory.IdemRes.exists_pow_eq_span P.asIdeal P.ne_bot
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)
  refine h x (Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x)) hx0 fun Q => ?_
  rw [GlobalTheory.PlaceIdem.mul_ap]
  by_cases hQ : a Q = 0
  · rw [hQ, zero_mul, map_zero]; exact zero_le
  · rw [h01 Q hQ, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one Q hx0]
    intro hxQ
    have := Q.isPrime
    have h1 : P.asIdeal ^ n ≤ Q.asIdeal := by rw [hx]; exact (Ideal.span_singleton_le_iff_mem _).2 hxQ
    have h2 : P.asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    have h3 : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h2)
    exact hQ (h3 ▸ h0)

variable {D : D7}

theorem exists_conj_mem {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {x : 𝓞 D.host.E}
    (hx : x ∈ P'.asIdeal) : ∃ y ∈ P.asIdeal, D.sp.cm.sig (y : D.host.E) = (x : D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hs : ∀ y, (s y : D.host.E) = star (y : D.host.E) := fun _ => rfl
  have hle : P.asIdeal ≤ P'.asIdeal.comap s := fun c hc => by
    obtain ⟨c', hc', e⟩ := h c hc
    have : s c = c' := RingOfIntegers.ext (by rw [hs, e])
    rw [Ideal.mem_comap, this]; exact hc'
  have he := P.isMaximal.eq_of_le (Ideal.comap_ne_top s P'.isPrime.ne_top) hle
  have hss : s (s x) = x := RingOfIntegers.ext (by rw [hs, hs, star_star])
  refine ⟨s x, ?_, congrArg Subtype.val hss⟩
  rw [he, Ideal.mem_comap, hss]; exact hx

section
variable (ι : (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  (h1 : ∀ x : D.host.E, ι ((1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
  (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
include h1 h2

theorem comp_eq_one {f : AE D} (hf : f * f = f) (P : Pl D.host.E)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 → finPart D (f * incA D ((x : D.host.E)⁻¹)) ∉ intAE D) :
    ι (finPart D f) P = 1 := by
  refine idem_apply_eq_one P _ (by rw [← map_mul, ← RingHom.map_mul, hf]) fun x hx hx0 hc => h x hx hx0 ?_
  have e : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
  rw [h2, RingHom.map_mul, map_mul, e, h1]
  exact hc

theorem comp_idem {f : AE D} {P : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P) : ι (finPart D f) P = 1 :=
  comp_eq_one ι h1 h2 hf.1.1 P fun x hx hx0 => (hf.2 x hx0).1 hx

theorem comp_conj_idem {f : AE D} {P P' : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P)
    (hc : Formalism.IndefR.Lev.IsConjPl P P') : ι (finPart D (cA D f)) P' = 1 := by
  refine comp_eq_one ι h1 h2 (by rw [← RingHom.map_mul, hf.1.1]) P' fun x hx hx0 hi => ?_
  obtain ⟨y, hy, hyx⟩ := exists_conj_mem hc hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (RingOfIntegers.ext (hyx.symm.trans (map_zero _)))
  refine (hf.2 y hy0).1 hy ?_
  have e : cA D (incA D ((y : D.host.E)⁻¹)) = incA D ((x : D.host.E)⁻¹) := by
    rw [← hyx, ← map_inv₀ D.sp.cm.sig]; rfl
  rw [← e, ← RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA] at hi
  have := GlobalTheory.PlaceIdem.sig_mem D hi
  rwa [GlobalTheory.PlaceIdem.sig_sig] at this

end

theorem exists_idem_mul {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f PP ∧ f * (e + cA D e) = f ∧ cA D f * (e + cA D e) = cA D f := by
  obtain ⟨⟨es, h1, h2⟩, h3⟩ := he
  have h4 : es PP * e = es PP := by
    rw [h2]
    refine GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => ?_) hPP
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]
  have h5 : es PP * (e + cA D e) = es PP := by
    rw [mul_add, h4, ← h4, mul_assoc, h3, mul_zero, add_zero]
  refine ⟨es PP, h1 PP hPP, h5, ?_⟩
  have h6 := congrArg (cA D) h5
  rwa [RingHom.map_mul, RingHom.map_add, cA_cA, add_comm] at h6

theorem unrOff_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  intro D c χ P₀ e hc he hu x hx1 hx2 hx3 hb
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hone : ∀ (f : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), f * (e + cA D e) = f → ι (finPart D f) P = 1 →
      ι (finPart D (x : AE D)) P = 1 := by
    intro f P hf hP
    have e1 : f * (x : AE D) = f := by rw [← hf, mul_assoc, hb]
    have e2 : ι (finPart D f) * ι (finPart D (x : AE D)) = ι (finPart D f) := by
      rw [← map_mul, ← RingHom.map_mul, e1]
    have e3 : ι (finPart D f) P * ι (finPart D (x : AE D)) P = ι (finPart D f) P :=
      congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e2
    rwa [hP, one_mul] at e3
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 1 → χ.UnrAt P := by
    intro P hP
    refine hu P (fun hm => hP ?_) fun PP hm hcj => hP ?_
    · obtain ⟨f, f1, f2, -⟩ := exists_idem_mul he hm
      exact hone f P f2 (comp_idem ι h1 h2 f1)
    · obtain ⟨f, f1, -, f3⟩ := exists_idem_mul he hm
      exact hone _ P f3 (comp_conj_idem ι h1 h2 f1 hcj)
  have key := hprod x hx1 S (fun P => if ι (finPart D (x : AE D)) P = 1 then 1 else k P) (fun P hP => by
    by_cases h : ι (finPart D (x : AE D)) P = 1
    · rw [if_pos h, h, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
    · rw [if_neg h]
      exact ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  by_cases h : ι (finPart D (x : AE D)) P = 1
  · rw [if_pos h, map_one, Units.val_one]
  · rw [if_neg h]
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [hv P] at a'
    have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    show ((χ.loc P (Formalism.L2.Host.atFin P (k P)) : ℂˣ) : ℂ) = 1
    rw [hunr P h _ hun, Units.val_one]

end GlobalTheory.ChrOff
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie




namespace GlobalTheory.SplitIdx


open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting in
theorem relIndex_half_act : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (ε : AE D), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS → GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT → ∀ g : GA D T, (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) = (GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).relIndex ((GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).map (GlobalTheory.SplitIdx.mulL (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT g).1)) := by
  intro D S T v φ ε hε BS BT hS hT g
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ ε hε).1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SplitHomLattice.mem_latO_iff_intM ε v (rdA φ) hε.1 hch S T BS BT hS hT
  have hL : ∀ V : HSp D, ((frameLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) = L0c D V := by
    intro V
    ext x
    show V.frame.equivFun.symm x ∈ V.L0 ↔ _
    rw [Module.Basis.equivFun_symm_apply]
    rfl
  set Hf := GlobalTheory.PlaceModel.half S T ε with hHf
  set P := (grpCo φ T BT g).1 with hP
  let Ψ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    AddMonoidHom.mk' (fun u => c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)) (fun x y => by
      simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add])
  have hΨ : ∀ u, Ψ u = c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1) := fun _ => rfl
  have hmemH : ∀ u ∈ Hf, (u ∈ halfLat S T ε ↔ Ψ u ∈ intMat D.host.F v T.rank S.rank) := by
    intro u hu
    have hu' : IsHalf ε u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    rw [halfLat, AddSubgroup.mem_inf, hL S, hL T, hΨ]
    constructor
    · rintro ⟨h, -⟩ i j
      exact GlobalTheory.SplitHecke.isInt_Ov.1 ((hc u hu').1 h i j)
    · intro h
      exact ⟨(hc u hu').2 fun i j => GlobalTheory.SplitHecke.isInt_Ov.2 (h i j), hu⟩
  have hmt1 : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hA : ∀ u, Ψ (actL S T g u) = P * Ψ u := by
    intro u
    change Ψ (actO S T 1 g u) = _
    rw [actO, hmt1, Matrix.mul_one, hΨ, hΨ, hP, grpCo, Matrix.mul_smul]
    congr 1
    rw [Matrix.map_mul]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc BT.1, Units.mul_inv, Matrix.one_mul]
    rfl
  have hAHf : ∀ u ∈ Hf, actL S T g u ∈ Hf := by
    intro u hu
    have hu' := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    refine (GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_
    show ε * actO S T 1 g u i j = actO S T 1 g u i j
    rw [actO, hmt1, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (mul_left_comm ε _ _).trans (congrArg (Formalism.L2.Theta.mt T g i k * ·) (hu' k j))
  let f : Hf →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := Ψ.comp Hf.subtype
  have hbij := GlobalTheory.PlaceCoord.bijOn_map (S := S) (T := T) hch hε.1.1 hε.2.2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : Ψ x = Ψ y := hxy
    rw [hΨ, hΨ] at hxy'
    have h1 : (BT⁻¹).1 * (x : WO S T).map (rdA φ) * BS.1 = (BT⁻¹).1 * (y : WO S T).map (rdA φ) * BS.1 :=
      smul_right_injective (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) hc0 hxy'
    have h2 := congrArg (fun M => BT.1 * M * (BS⁻¹).1) h1
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
    exact Subtype.ext (hbij.injOn ((GlobalTheory.PlaceModel.isHalf_iff S T).2 x.2) ((GlobalTheory.PlaceModel.isHalf_iff S T).2 y.2) h2)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht, ht'⟩ := GlobalTheory.PlaceCoord.exists_half hch hε.1.1 hε.2.2 (c⁻¹ • (BT.1 * y * (BS⁻¹).1))
    refine ⟨⟨t, (GlobalTheory.PlaceModel.isHalf_iff S T).1 ht⟩, ?_⟩
    change Ψ t = y
    rw [hΨ, ht', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hH : halfLat S T ε ≤ Hf := inf_le_right
  have hK : (halfLat S T ε).map (actL S T g) ≤ Hf := by
    rintro _ ⟨u, hu, rfl⟩
    exact hAHf u (hH hu)
  have e1 : ((halfLat S T ε).addSubgroupOf Hf).map f = intMat D.host.F v T.rank S.rank := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmemH w w.2).1 (AddSubgroup.mem_addSubgroupOf.1 hw)
    · intro hy
      obtain ⟨w, hw⟩ := hf_surj y
      refine ⟨w, AddSubgroup.mem_addSubgroupOf.2 ((hmemH w w.2).2 ?_), hw⟩
      exact hw ▸ hy
  have e2 : (((halfLat S T ε).map (actL S T g)).addSubgroupOf Hf).map f =
      (intMat D.host.F v T.rank S.rank).map (mulL P) := by
    ext y
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, hw⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_addSubgroupOf.1 hw)
      refine ⟨Ψ u, (hmemH u (hH hu)).1 hu, ?_⟩
      change P * Ψ u = Ψ (w : WO S T)
      rw [← hw, hA]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hf_surj z
      have hz' : Ψ w ∈ intMat D.host.F v T.rank S.rank := hw ▸ hz
      refine ⟨⟨actL S T g w, hAHf w w.2⟩, AddSubgroup.mem_addSubgroupOf.2 ⟨w, (hmemH w w.2).2 hz', rfl⟩, ?_⟩
      change Ψ (actL S T g w) = mulL P z
      rw [hA w, ← hw]
      rfl
  rw [← AddSubgroup.relIndex_addSubgroupOf hK, ← AddSubgroup.relIndex_map_map_of_injective _ _ hf_inj, e1, e2]

end GlobalTheory.SplitIdx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  first | exact @GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | exact GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | (intros; apply GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW <;> assumption)
end

section


theorem _root_.GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.GeometricLemma := by
  first | exact @GlobalTheory.geometricLemma_of_filtration | exact GlobalTheory.geometricLemma_of_filtration | (intros; apply GlobalTheory.geometricLemma_of_filtration <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  first | exact @GlobalTheory.LocalInvIdem.exists_inv | exact GlobalTheory.LocalInvIdem.exists_inv | (intros; apply GlobalTheory.LocalInvIdem.exists_inv <;> assumption)
end
