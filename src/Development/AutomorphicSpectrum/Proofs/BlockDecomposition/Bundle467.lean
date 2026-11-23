module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle425
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle411
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsAbs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle436
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.DegLam

section Abstract

variable {R : Type} [CommRing R] {n k : ℕ}

def compress (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) : GL (Fin k) R :=
  have key : ∀ u v : GL (Fin n) R, u * v = 1 → u.val * (A * N) = (A * N) * u.val →
      (N * u.val * A) * (N * v.val * A) = 1 := by
    intro u v huv hu
    have h1 : u.val * v.val = 1 := by rw [← Units.val_mul, huv, Units.val_one]
    calc (N * u.val * A) * (N * v.val * A) = N * (u.val * (A * N)) * v.val * A := by
          simp only [Matrix.mul_assoc]
      _ = N * (A * N) * (u.val * v.val) * A := by
          rw [hu]; simp only [Matrix.mul_assoc]
      _ = (N * A) * (N * A) := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = 1 := by rw [hNA, Matrix.mul_one]
  { val := N * t.val * A
    inv := N * (t⁻¹ : GL (Fin n) R).val * A
    val_inv := key t t⁻¹ (mul_inv_cancel t) ht
    inv_val := mul_eq_one_comm.1 (key t t⁻¹ (mul_inv_cancel t) ht) }

theorem compress_val (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    (compress A N hNA t ht).val = N * t.val * A := rfl

theorem mul_frame (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    t.val * A = A * (compress A N hNA t ht).val := by
  rw [compress_val]
  calc t.val * A = t.val * (A * (N * A)) := by rw [hNA, Matrix.mul_one]
    _ = (t.val * (A * N)) * A := by simp only [Matrix.mul_assoc]
    _ = A * (N * t.val * A) := by rw [ht]; simp only [Matrix.mul_assoc]

theorem det_compress (A : Matrix (Fin n) (Fin k) R) (N : Matrix (Fin k) (Fin n) R) (hNA : N * A = 1)
    (t : GL (Fin n) R) (ht : t.val * (A * N) = (A * N) * t.val) :
    (compress A N hNA t ht).val.det = (1 + (A * N) * (t.val - 1)).det := by
  rw [compress_val, Matrix.mul_assoc A N, Matrix.det_one_add_mul_comm, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hNA, add_sub_cancel]

end Abstract

section Image

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem linInd_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ := by
  have h := (Module.finBasis E W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have h1 : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    ext j i
    simp [basisMat]
  rw [h1]
  exact h

theorem exists_coord (W : Submodule E (Fin n → E)) (w : Fin n → E) (hw : w ∈ W) :
    ∃ c, basisMat W *ᵥ c = w := by
  refine ⟨(Module.finBasis E W).repr ⟨w, hw⟩, ?_⟩
  have h := (Module.finBasis E W).sum_repr ⟨w, hw⟩
  ext i
  have h2 : ((∑ j, (Module.finBasis E W).repr ⟨w, hw⟩ j • Module.finBasis E W j : W) : Fin n → E) i = w i := by
    rw [h]
  rw [Submodule.coe_sum, Finset.sum_apply] at h2
  rw [← h2]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by simp [basisMat, mul_comm]

theorem idem_mul_basisMat {e : Matrix (Fin n) (Fin n) E} (he : e * e = e) :
    e * basisMat (LinearMap.range (Matrix.toLin' e)) = basisMat (LinearMap.range (Matrix.toLin' e)) := by
  ext i j
  have h := (mem_range_idem he _).1
    (Module.finBasis E (LinearMap.range (Matrix.toLin' e)) j).2
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, basisMat] using congrFun h i

theorem basisMat_mul_idem {e : Matrix (Fin n) (Fin n) E}
    {L : Matrix (Fin (Module.finrank E (LinearMap.range (Matrix.toLin' e)))) (Fin n) E}
    (hL : L * basisMat (LinearMap.range (Matrix.toLin' e)) = 1) :
    basisMat (LinearMap.range (Matrix.toLin' e)) * (L * e) = e := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨c, hc⟩ := exists_coord (LinearMap.range (Matrix.toLin' e)) (e *ᵥ y)
    ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hc, Matrix.mulVec_mulVec c L, hL, Matrix.one_mulVec]

end Image

theorem deg_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), DegAdelic →
    ∀ (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t x : GA E n, t.val * rm e = rm e * t.val →
      deg (t * x) (LinearMap.range (Matrix.toLin' e)) = deg x (LinearMap.range (Matrix.toLin' e)) + lam e t := by
  intro E _ _ _ n hA e he t x ht
  have hM := linInd_basisMat (LinearMap.range (Matrix.toLin' e))
  obtain ⟨L, hLM⟩ := GlobalTheory.CompanionTheory.DegAdelicProof.exists_leftInv _ hM
  have hNM : (L * e) * basisMat (LinearMap.range (Matrix.toLin' e)) = 1 := by
    rw [Matrix.mul_assoc, idem_mul_basisMat he, hLM]
  have hBA : (L * e).map (algebraMap E (Ad E)) *
      (basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAB : (basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E)) = rm e := by
    rw [← Matrix.map_mul, basisMat_mul_idem hLM]
    rfl
  have ht' : t.val * ((basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E))) = ((basisMat (LinearMap.range (Matrix.toLin' e))).map (algebraMap E (Ad E)) *
      (L * e).map (algebraMap E (Ad E))) * t.val := by
    rw [hAB]
    exact ht
  have h := hA E n _ x t (compress _ _ hBA t ht') _ hM (mul_frame _ _ hBA t ht')
  have hd := det_compress _ _ hBA t ht'
  rw [hAB] at hd
  unfold deg lam chi
  rw [← hd]
  exact h

end GlobalTheory.CompanionTheory.TorusCh.DegLam

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CommMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_sq_eq_one : (thetaA E n) ^ 2 = 1 := by
  ext g : 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (thetaR (conjAd E) n (thetaR (conjAd E) n g)).val i j = g.val i j
  rw [thetaR_val]
  have h : (thetaR (conjAd E) n g)⁻¹ = thetaR (conjAd E) n g⁻¹ := (map_inv _ _).symm
  rw [h, thetaR_val, inv_inv]
  simp [GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol]

theorem twNorm_ratGL (d : GL (Fin n) E) :
    twNorm (thetaA E n) 2 (ratGL E n d) = ratGL E n (nrm d) := by
  rw [nrm, map_mul, ← GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL]
  simp [twNorm]

theorem rm_algebraMap (a : E) :
    rm (algebraMap E (Matrix (Fin n) (Fin n) E) a) =
      algebraMap (Ad E) (Matrix (Fin n) (Fin n) (Ad E)) (algebraMap E (Ad E) a) := by
  ext i j
  by_cases h : i = j <;> simp [rm, Matrix.algebraMap_matrix_apply, h]

theorem comm_rm_aeval (x : Matrix (Fin n) (Fin n) (Ad E)) (γ : Matrix (Fin n) (Fin n) E)
    (hx : x * rm γ = rm γ * x) (f : E[X]) : x * rm (aeval γ f) = rm (aeval γ f) * x := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, rm_algebraMap]
    exact (Algebra.commutes _ x).symm
  | add p q hp hq =>
    rw [map_add (f := _), rm_add, mul_add, add_mul, hp, hq]
  | monomial m a h =>
    have e : aeval γ (C a * X ^ (m + 1)) = aeval γ (C a * X ^ m) * γ := by
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, rm_mul, ← mul_assoc, h, mul_assoc, hx, mul_assoc]

theorem adCent_comm_rm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  intro E _ _ _ n d t ht e he
  obtain ⟨f, rfl⟩ := he
  refine comm_rm_aeval _ _ ?_ f
  have h := twCent_commute_twNorm (thetaA E n) thetaA_sq_eq_one (ratGL E n d) ht
  rw [twNorm_ratGL] at h
  exact congrArg Units.val h

end GlobalTheory.CompanionTheory.TorusCh.CommMem

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

universe w w' u₁ v₁ u₂ v₂ u₃ v₃

theorem pull_transport' {R : Type} [CommRing R] {Th : Type u₁} [Category.{v₁} Th] {Ec : Type u₂} [Category.{v₂} Ec]
    {C : Type u₃} [Category.{v₃} C]  (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : CH.Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : CH.H F 2) {Pc : CH.Cn ((G ⋙ m.G) ⋙ F) 2 → Prop} (h : ∃ (c : CH.Cn ((G ⋙ m.G) ⋙ F) 2) (hc : CH.d _ 2 c = 0), (CH.cx _).cls c hc = (CH.Mor.restrict F (G ⋙ m.G)).pull 2 x ∧ Pc c)
    (P : CH.Cn (G ⋙ F') 2 → Prop) (hP : ∀ z : CH.Cn (G ⋙ F') 2, ∀ c, (∀ s, z s = m.τ _ (c s)) → Pc c → P z) :
    ∃ (z : CH.Cn (G ⋙ F') 2) (hz : CH.d (G ⋙ F') 2 z = 0), P z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  obtain ⟨c, hc, h, hp⟩ := h
  obtain ⟨hz, e⟩ := pull_transport F F' m G x c hc h
  exact ⟨_, hz, hP _ c (fun _ => rfl) hp, e⟩

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X} (k : Bool) (n : ℕ)

theorem st1 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (c : CH.Cn (gG k n G ⋙ OM _ ((PAlg.base l).cris n)) 2) (hz : CH.d _ 2 c = 0),
      (CH.cx _).cls _ hz = (CH.Mor.restrict (OM _ ((PAlg.base l).cris n)) (gG k n G)).pull 2 (x n) ∧
      c = (lam k n Λ).coc ((PAlg.base l).cris n) (l * n) := by
  have h := hx n C (gG k n G) (lam k n Λ)
  exact ⟨_, h.choose, h.choose_spec, rfl⟩

theorem st2 (Λ : E.Lift G D) (s : ComposableArrows C 2) (y : (G.obj (s.obj (Fin.last 2))).1.obj.Acr n)
    (hy : y = dlog (DD k (G.obj (s.obj (Fin.last 2))).1.obj n) (l * n) ((lam k n Λ).r s).val) :
    E.IsLog (G.obj (s.obj (Fin.last 2))).1.obj n (E.tei (G.obj (s.obj (Fin.last 2))).1.obj (Λ.r s)) y := by
  rw [hy]
  have h1 : (G.obj (s.obj (Fin.last 2))).1.obj.sharp (Λ.r s).val = 1 :=
    sharp_r Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← Functor.map_comp]; rfl)
  exact isLog_dlog k _ n _ h1 _ (lam_r k n Λ s)

theorem st3 (Λ : E.Lift G D) (x : ∀ n, Hc (schFn q) κ k n 2) (hx : IsFirstChernFamily q D κ k x) :
    ∃ (z : CH.Cn (G ⋙ CH.modF (AcrEl (PX q κ) n)) 2) (hz : CH.d _ 2 z = 0), Λ.IsCoc n z ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (CH.modF (AcrEl (PX q κ) n)) G).pull 2 (β (schFn q) κ k n 2 (x n)) :=
  pull_transport' (Oc (schFn q) κ k n) (CH.modF (AcrEl ((schFn q).pt κ) n)) (βMor (schFn q) κ k n) G (x n)
    (st1 k n Λ x hx) (fun z => Λ.IsCoc n z) (fun z c hs hc s => st2 k n Λ s _ ((hs s).trans (congrArg _ (congrFun hc s))))
end

theorem main : ∀ (l : ℕ) [Fact l.Prime], FirstChernCompatible l := by
  intro l _ O _ X q κ k D x hx C _ G Λ n
  exact st3 k n Λ x hx

end GlobalTheory.CompanionTheory.FirstChernComparison
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

def whitT (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (T : Mx D n n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) ∂lam

def WhitKA : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
  ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
    HolValueAt (whitT ψ V μ lam nb w H (ω k Φ).1 (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n)
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β)

end GlobalTheory.CompanionTheory.IwaAd
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem pow_mem_map {R B : Type} [CommRing R] [CommRing B] (h : R →+* B) (I : Ideal R) (p : ℕ) (hp : p.Prime)
    (hI : ∀ x ∈ I, x ^ p ∈ Ideal.span {(p : R)}) : ∀ x ∈ I.map h, x ^ p ∈ Ideal.span {(p : B)} := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => x ^ p ∈ Ideal.span {(p : B)}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hI y hy)
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [zero_pow hp.ne_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
    rw [hr]
    exact add_mem (add_mem ha hb) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))))
  · intro a b _ hb
    rw [smul_eq_mul, mul_pow]
    exact Ideal.mul_mem_left _ _ hb

section Tens

variable {R S T C B : Type} [CommRing R] [CommRing S] [CommRing T] [CommRing C] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra R C] [Algebra S C] [Algebra T C]
  [IsScalarTower R S C] [IsScalarTower R T C]


open TensorProduct in
theorem tens_ext
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (f f' : C →+* B) (h1 : ∀ s, f (algebraMap S C s) = f' (algebraMap S C s))
    (h2 : ∀ t, f (algebraMap T C t) = f' (algebraMap T C t)) : f = f' := by
  refine RingHom.ext fun c => ?_
  obtain ⟨z, rfl⟩ := hs c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom',
      map_mul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]


open TensorProduct in
theorem tens_desc (m n : ℕ)
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (hk : ∀ z : S ⊗[R] T, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _) z = 0 ↔
        z ∈ Ideal.span {(m : S ⊗[R] T) ^ n})
    (u : S →+* B) (v : T →+* B) (huv : ∀ r, u (algebraMap R S r) = v (algebraMap R T r))
    (hm : (m : B) ^ n = 0) :
    ∃ f : C →+* B, (∀ s, f (algebraMap S C s) = u s) ∧ ∀ t, f (algebraMap T C t) = v t := by
  letI : Algebra R B := (u.comp (algebraMap R S)).toAlgebra
  let u' : S →ₐ[R] B := { u with commutes' := fun _ => rfl }
  let v' : T →ₐ[R] B := { v with commutes' := fun r => (huv r).symm }
  let L : S ⊗[R] T →ₐ[R] B := Algebra.TensorProduct.lift u' v' (fun _ _ => Commute.all _ _)
  let Φ : S ⊗[R] T →ₐ[R] C := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
    (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)
  have hker : RingHom.ker (Φ : S ⊗[R] T →+* C) ≤ RingHom.ker (L : S ⊗[R] T →+* B) := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((hk z).1 hz)
    rw [RingHom.mem_ker, map_mul, map_pow, map_natCast, hm, mul_zero]
  let f : C →+* B := (Φ : S ⊗[R] T →+* C).liftOfSurjective hs ⟨(L : S ⊗[R] T →+* B), hker⟩
  have hf : ∀ z, f (Φ z) = L z := fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z
  refine ⟨f, fun s => ?_, fun t => ?_⟩
  · have h := hf (s ⊗ₜ 1)
    simpa [Φ, L, u'] using h
  · have h := hf (1 ⊗ₜ t)
    simpa [Φ, L, v'] using h

end Tens

end GlobalTheory.CompanionTheory.AcrUniv

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem maps_out : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  intro l _ A n B _ h
  have hp : l.Prime := Fact.out
  obtain ⟨⟨π, -, -⟩, hFil, -, -, -, -, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  obtain ⟨-, -, -, -, -, hpow, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal (base l) n
  have hlB : (l : B) ^ n = 0 := by
    rw [← map_natCast h, ← map_pow, pow_l_acr, map_zero]
  have hlJ : (l : B) ∈ ((base l).PFil n).map h := by
    rw [← map_natCast h]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hJp : ∀ x ∈ ((base l).PFil n).map h, x ^ l ∈ Ideal.span {(l : B)} :=
    pow_mem_map h _ l hp fun x hx => (hpow x hx).2
  have hOb : D.Pf l (Ob l) := ⟨(base l).natCast_l, (base l).perf.1⟩
  have hA : D.Pf l A.A := ⟨A.natCast_l, A.perf.1⟩
  obtain ⟨hts, htk⟩ := RL.tens A n
  have hbs := ((RL.base_acr (base l) isBase_base).2 n).1
  refine ⟨fun g hg => ?_, fun f f' h1 h2 h3 => ?_⟩
  · obtain ⟨⟨f₀, hf₀⟩, -⟩ := GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp g
    have hc : f₀.comp A.sW = h.comp ((base l).toAcr n) :=
      (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l (A := Ob l) _ n hOb hlB hlJ hJp (g.comp A.s)).2 _ _ fun a => by
        rw [RingHom.comp_apply, RingHom.comp_apply, sW, WittVector.map_teichmuller, hf₀]
        exact hg a
    have huv : ∀ r : Ainf l, (h.comp ((base l).cris n)) (algebraMap (Ainf l) (Acris l) r) =
        f₀ (algebraMap (Ainf l) A.W r) := fun r => by
      rw [RingHom.comp_apply, cris_algebraMap]
      have e : (base l).sW r = r := wmap_id r
      rw [e]
      exact (RingHom.congr_fun hc r).symm
    obtain ⟨f, hf1, hf2⟩ := tens_desc l n hts htk (h.comp ((base l).cris n)) f₀ huv hlB
    refine ⟨f, RingHom.ext fun y => ?_, fun a => ?_⟩
    · obtain ⟨a, rfl⟩ := hbs y
      rw [RingHom.comp_apply, mapAcr_cris]
      exact hf1 a
    · have e : f (A.toAcr n (WittVector.teichmuller l a)) = f₀ (WittVector.teichmuller l a) :=
        hf2 (WittVector.teichmuller l a)
      rw [e, hf₀]
  · have hfJ : A.PFil n ≤ (((base l).PFil n).map h).comap f := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact hlJ
      · rw [hFil 1, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply, h1]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hx)
    have hw := (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp
      ((Ideal.quotientMap _ f hfJ).comp π)).2 (f.comp (A.toAcr n)) (f'.comp (A.toAcr n))
      fun a => Ideal.Quotient.eq.2 (h3 a)
    refine tens_ext hts f f' (fun a => ?_) fun t => RingHom.congr_fun hw t
    have e : algebraMap (Acris l) (A.Acr n) a = mapAcr A.fromBase n ((base l).cris n a) :=
      (mapAcr_cris A.fromBase n a).symm
    rw [e]
    exact RingHom.congr_fun (h1.trans h2.symm) _

end GlobalTheory.CompanionTheory.AcrUniv
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.truncated_witt_isNoetherian : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l], IsNoetherianRing (Wc.Wm l k 1) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | exact GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | (intros; apply GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.finite_length_witt_cohomology : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | exact GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | (intros; apply GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one <;> assumption)
end
