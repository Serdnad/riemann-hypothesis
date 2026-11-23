module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle265
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

def ClsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (δ : ℤˣ) : Prop :=
  ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def IoAt (O : OMDat T.toCore R i Tp tup) (v₀ : (R.MW i (sg0 D A)).Vec) (ka : ℂ) : Prop :=
  ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v)))

def CovAt (O : OMDat T.toCore R i Tp tup) (c0 : ℂ) : Prop :=
  ∀ (t : Tp) (X : Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsSympl X bas → IdxIs O.c' (inC O.c') X idx e → latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → IsMark (O.dδ t).l₂ X.Λ mk → MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((R.xi (tup t) xk : Circle) : ℂ)

def degW {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

end GlobalTheory.PtId
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def cmpConst (D : D7) (ka : ℂ) (δ : ℤˣ) (d : ℕ) : ℂ :=
  ka * (((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d)



theorem cmpConst_ne_zero {ka : ℂ} (hka : ka ≠ 0) (δ : ℤˣ) (d : ℕ) : cmpConst D ka δ d ≠ 0 := by
  have h1 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have h2 : ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  have h3 : ((δ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 δ.ne_zero
  exact mul_ne_zero hka (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ (inv_ne_zero h2)))


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem ccIs_transport {θ : InfFam D} {V W : HSp D} {hr : W.rank = D.R.r} {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ')
    (hV : T.V j σ = W) (hV' : T.V j σ' = W) {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ}
    {cst : (T.U j σ).Comp → ℂ}
    (h : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.x₀ j σ) om f₀ cst) :
    ∃ cst' : (T.U j σ').Comp → ℂ,
      CcIs θ V W hr (T.U j σ') (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.x₀ j σ') om f₀ cst' ∧
      ∀ g, cst' (castDict hV' (T.dict j σ') g).1 = cst (castDict hV (T.dict j σ) g).1 := by
  subst e
  exact ⟨cst, h, fun _ => rfl⟩


end GlobalTheory.PtId
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.closure_frobeniusElements_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → (∀ (F : Type) [Field F] [NumberField F] [Algebra K F], (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  first | exact @GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | exact GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | (intros; apply GlobalTheory.Mem.FieldsEx.closure_frob_eq_top <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.exists_two_primes_same_norm_of_trivial_frobenius : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F] (σ : F ≃ₐ[K] F), σ ≠ 1 → ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 → ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | exact GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | (intros; apply GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.exists_generator_pow_prime_one_mod_modulus : ∀ (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ), 𝔮 ≠ ⊥ → (∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α}) → ∀ v : HeightOneSpectrum (𝓞 L), ∃ k : Lˣ, FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧ ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  first | exact @GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod | exact GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod | (intros; apply GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.absNorm_modEq_one_of_principal_rayClass : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  first | exact @GlobalTheory.Mem.RayNorm.absNorm_modEq_one | exact GlobalTheory.Mem.RayNorm.absNorm_modEq_one | (intros; apply GlobalTheory.Mem.RayNorm.absNorm_modEq_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharLoc

variable {F : Type} [Field F] [NumberField F]

theorem psiV_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F ψ v y = psiV F ψ₀ v (algebraMap F (Fv F v) a * y) := by
  rw [psiV, psiV, h]
  refine congrArg ψ₀ (Prod.ext (mul_zero _) ?_)
  show algebraMap F (Af F) a * singleV F v y = singleV F v _
  rw [mul_comm, GlobalTheory.SnMass.Inhab.single_mul, mul_comm]
  rfl

theorem psiInf_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (y : Ainf F) : psiInf F ψ y = psiInf F ψ₀ (algebraMap F (Ainf F) a * y) := by
  rw [psiInf, psiInf, h]
  exact congrArg ψ₀ (Prod.ext rfl (mul_zero _))

theorem eventually_integral (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem ne_one_of_stdAt {v : HeightOneSpectrum (𝓞 F)} {χ : Fv F v → ℂ} (hs : GlobalTheory.SnMass.StdAt v χ) :
    ∃ y, χ y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem eq_zero_of_std {ψ : AddChar (AF F) ℂ} (h : GlobalTheory.SnMass.IsStdChar F ψ) (z : Ainf F)
    (hz : ∀ y, psiInf F ψ (z * y) = 1) : z = 0 := by
  classical
  funext w
  by_contra hw
  have hw' : z w ≠ 0 := hw
  let y : Ainf F := Pi.single w ((z w)⁻¹ * 2⁻¹)
  have h1 := hz y
  rw [h.2.1, Finset.sum_eq_single w] at h1
  · have e : (z * y) w = 2⁻¹ := by
      show z w * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) w = _
      rw [Pi.single_eq_same, mul_inv_cancel_left₀ hw']
    rw [e, map_inv₀, map_ofNat] at h1
    have e2 : 2 * Real.pi * Complex.I * (((2⁻¹ : ℂ).re : ℝ) : ℂ) = Real.pi * Complex.I := by
      have : (2⁻¹ : ℂ).re = 2⁻¹ := by simp
      rw [this]
      push_cast
      ring
    rw [e2, Complex.exp_pi_mul_I] at h1
    norm_num at h1
  · intro u _ hu
    have e : (z * y) u = 0 := by
      show z u * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) u = _
      rw [Pi.single_eq_of_ne hu, mul_zero]
    rw [e, map_zero, Complex.zero_re]
  · intro hn
    exact absurd (Finset.mem_univ w) hn

theorem char_local : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  intro F _ _ _ ψ hψ
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 hψ
  refine ⟨fun v => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := ne_one_of_stdAt (h₀.2.2 v)
    refine ⟨algebraMap F (Fv F v) a⁻¹ * y, ?_⟩
    rwa [psiV_twist h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  · obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
    have hd1 : (d : F) ≠ 0 := by exact_mod_cast hd0
    filter_upwards [eventually_integral a, eventually_integral (a * d)⁻¹] with v h1 h2 y
    simp only [psiV_twist h, ← mul_assoc]
    refine (h₀.2.2 v _).trans ⟨fun hy => ?_, fun hy d' _ => ?_⟩
    · have h3 := mul_mem (hy d hd) h2
      rwa [mul_right_comm _ y, ← map_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hd1),
        map_one, one_mul] at h3
    · exact mul_mem (mul_mem h1 hy) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d')
  · have h1 := eq_zero_of_std h₀ (algebraMap F (Ainf F) a * x) fun y => by
      rw [mul_assoc, ← psiInf_twist h, hx]
    have h2 := congrArg (algebraMap F (Ainf F) a⁻¹ * ·) h1
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_zero] using h2

end GlobalTheory.GaugeEx.CharLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isotypicSum_inf_groupAlgebraKilled_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  first | exact @GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot | exact GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot | (intros; apply GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.rank_equivariantHomsInto_isotypicSum_of_iso : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) → Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  first | exact @GlobalTheory.MultIso.rank_homInto_iSup_range | exact GlobalTheory.MultIso.rank_homInto_iSup_range | (intros; apply GlobalTheory.MultIso.rank_homInto_iSup_range <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.nonempty_iso_of_equivariantHom_into_isotypicSum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  first | exact @GlobalTheory.IsoRankMult.iso_of_hom_into_sum | exact GlobalTheory.IsoRankMult.iso_of_hom_into_sum | (intros; apply GlobalTheory.IsoRankMult.iso_of_hom_into_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

theorem GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ)
    (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) : ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧
      CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ Y₁.Fn (ratOf Y₁).pt
  obtain ⟨q, ⟨hq, hqb⟩, -⟩ := h₂.2.2 Y₁.Fn ((ratOf Y₁).pt ≫ f₁) A hA h hh
  have hcq : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q := ⟨A, hA, h, hh, hb, hqb⟩
  obtain ⟨B, hB, g, hg, hgb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ h₂ Y₂.Fn (ratOf Y₂).pt
  obtain ⟨r, ⟨hr, hrb⟩, -⟩ := h₁.2.2 Y₂.Fn ((ratOf Y₂).pt ≫ f₂) B hB g hg
  have hcr : CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt := ⟨B, hr ▸ hB, g, hg, hrb, hgb⟩
  have hsp := GlobalTheory.T.fullFlagLift_genericPoint_specializes_residue F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hcq (r (IsLocalRing.closedPoint _))
    (fun K _ p p' hp hpp hc => GlobalTheory.T.fullFlagBundle_point_at_genericLift_image F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ r hr hcr K p p' hp hpp hc)
  have hs : q ≫ Y₂.str = spMap (algebraMap F Y₁.Fn) := by
    have e1 : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
    have e2 : f₁ ≫ X.str = Y₁.str := h₁.1.inducedModelMorphism_comp_structureMap
    have e3 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ Y₁.str = spMap (algebraMap F Y₁.Fn) := (ratOf Y₁).pt_s
    calc q ≫ Y₂.str = q ≫ (f₂ ≫ X.str) := congrArg (q ≫ ·) e1.symm
    _ = (q ≫ f₂) ≫ X.str := (Category.assoc _ _ _).symm
    _ = ((ratOf Y₁).pt ≫ f₁) ≫ X.str := congrArg (· ≫ X.str) hq
    _ = (ratOf Y₁).pt ≫ (f₁ ≫ X.str) := Category.assoc _ _ _
    _ = (ratOf Y₁).pt ≫ Y₁.str := congrArg (((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ ·) e2
    _ = _ := e3
  obtain ⟨ψ, rfl⟩ := GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint F Y₂ Y₁.Fn q hsp hs
  refine ⟨ψ, ?_, hcq⟩
  have key : ∀ (σ : X.Fn →+* Y₁.Fn) (a : X.Fn), (ratOf X).val (spMap σ ≫ (ratOf X).pt) a = σ a := by
    intro σ a
    have hm : a ∈ (ratOf X).O (genericPoint (ratOf X).Z) :=
      (RatModel.O_genericPoint (ratOf X)).symm ▸ Algebra.mem_top
    have h1 := RatModel.val_spMap_comp σ (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    have h2 := RatModel.valLoc_eq_val (M := ratOf X) (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    exact h1.trans (congrArg σ (h2.trans (RatModel.val_pt (M := ratOf X) a)))
  have H1 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ f₁ = spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₁.1
  have H2 : ((ratOf Y₂).pt : Sp Y₂.Fn ⟶ Y₂.X) ≫ f₂ = spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₂.1
  have e : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) =
      spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := by
    have s1 : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)
        = spMap ψ.toRingHom ≫ (spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)) := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    exact s1.trans ((congrArg (spMap ψ.toRingHom ≫ ·) H2.symm).trans
      ((Category.assoc _ _ _).symm.trans (hq.trans H1)))
  ext a
  have := congrArg (fun y => (ratOf X).val y a) e
  simp only [key] at this
  exact this
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

theorem isOrthF_one {D : D7} (V : HSp D) (h : V.gram = 1) : GlobalTheory.StdFrameExist.IsOrthF V 1 := by
  unfold GlobalTheory.StdFrameExist.IsOrthF GlobalTheory.StdFrameExist.gA
  rw [h, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]

theorem intM_one {D : D7} (n : ℕ) : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (1 : GL (Fin n) (Lev.EAf D)).1 := by
  intro i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_unit_frame : ∀ (D : D7) (V : HSp D) (hF : D.host.F = maximalRealSubfield D.host.E), V.gram = 1 → Seed.FrmC.StdLat V → ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame hF P ∧ UnitFr P := by
  intro D V hF hg hV
  have h := isOrthF_one V hg
  refine ⟨GlobalTheory.StdFrameExist.rowPsi V 1 h, GlobalTheory.StdFrameExist.stdFrame_rowPsi hF hV h (intM_one _) ?_, fun κ => ?_⟩
  · rw [inv_one]; exact intM_one _
  · show finE V (GlobalTheory.StdFrameExist.psiF V 1 h κ) = _
    rw [GlobalTheory.StdFrameExist.finE_psiF, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.MtIn
end
end
