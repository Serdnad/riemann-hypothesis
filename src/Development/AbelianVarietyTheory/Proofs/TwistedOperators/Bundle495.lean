module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle461
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.HeisLineTransfer

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

end GlobalTheory.HeisLineTransfer

namespace GlobalTheory.HeisLineTransfer



theorem isDatum_dRho_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hc g φ hφ hvac f hf τ z g₁ hact
  subst hψ
  obtain ⟨hΦ, hfΦ⟩ := hf
  have hF : IsTotallyReal D.host.F := hBs.cm.1
  have hψc : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hstd : ∀ᶠ v in Filter.cofinite, φ v =
      Set.indicator {x : Fin S.rank × Fin d → v.adicCompletion D.host.F | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have h1 := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  refine ⟨h1, fun u => ?_⟩

  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  have hform : ∀ w w' : Matrix (Fin S.rank) (Fin d) (AE D), symplO (sgn ε S) X (cS w) (cS w') =
      (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 := by
    intro w w'
    rw [← GlobalTheory.WeilSchrodinger.symp_eq_symplO D (sgn ε S) X X.gramᵀ (D.host.xi0 • (sgn ε S).gram⁻¹) 1 rfl
      (one_smul _ _), co.form, hco, hco]

  obtain ⟨hline, -⟩ := GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z
  set u₀ := cS.symm (lineAt θ τ z 1) with hu₀
  have hcs : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hc, hc, ← Matrix.smul_mul]
    rfl
  have hL : ∀ t : ℝ, lineAt θ τ z t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) := by
    intro t
    rw [hcs, hu₀, AddEquiv.apply_symm_apply, hline]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num)).symm

  have hkey : ∀ t : ℝ, heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u) =
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
    intro t
    set u' := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀
    have e1 : ∀ x, M.co.rho Bs.ψ u (M.co.rho Bs.ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x =
        Bs.ψ (⅟(2 : AF D.host.F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2)) *
          M.co.rho Bs.ψ (u + u') (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x := by
      intro x
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_schr_apply Bs.ψ _ _ _ x
    rw [hL t]
    simp only [heisO]
    rw [← map_add (f := _), ← hfΦ (u + u')]
    simp only [GlobalTheory.WeilM.thetaSum, e1, tsum_mul_left]
    rw [symplOH, hform, h2]

  have hd : ∀ x, HasDerivAt
      (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ x) 0 :=
    fun x => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) x
  have hder : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F
      (M.co.rho Bs.ψ u (M.co.rho Bs.ψ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
      (GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul] at hd ⊢
    exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hF hψc (M.co.e u₀) hΦ h1 hd (M.co.e u)
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ)) =
    Formalism.IndefR.Datum.dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f (cS u)
  have hfun : (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u
        (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := funext hkey
  unfold Formalism.IndefR.Datum.dRho
  rw [hfun]
  exact hder.deriv.symm

end GlobalTheory.HeisLineTransfer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KInvData

theorem hasDerivAt_linear {Z Q : Type} [NormedAddCommGroup Q] [NormedSpace ℂ Q] (U : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ U] (φ : (Z → ℂ) →ₗ[ℂ] Q) {u : ℝ → Z → ℂ} {u' : Z → ℂ} {t : ℝ} (hu : ∀ s, u s ∈ U) (hu' : u' ∈ U)
    (hd : ∀ z, HasDerivAt (fun s => u s z) (u' z) t) : HasDerivAt (fun s => φ (u s)) (φ u') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Filter.Tendsto (slope u t) (nhdsWithin t {t}ᶜ) (nhds u') := by
    rw [tendsto_pi_nhds]
    intro z
    exact hasDerivAt_iff_tendsto_slope.1 (hd z)
  have hm : ∀ s, slope u t s ∈ U := fun s => U.smul_of_tower_mem _ (U.sub_mem (hu s) (hu t))
  have h2 : Filter.Tendsto (fun s => (⟨slope u t s, hm s⟩ : U)) (nhdsWithin t {t}ᶜ) (nhds ⟨u', hu'⟩) :=
    tendsto_subtype_rng.2 h1
  have h3 := ((φ ∘ₗ U.subtype).continuous_of_finiteDimensional.tendsto _).comp h2
  refine h3.congr fun s => ?_
  simp [slope, LinearMap.map_smul_of_tower]

theorem kapX_one {D : D7} (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
  {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
  {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO W X → ℂ) →ₗ[ℂ] Pi}

theorem line_step (hθ : IsInfFam θ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hmap : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p)
    {τ : D.what₂.Tau} {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ)
    (U : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ)) [FiniteDimensional ℂ U]
    (hU : U ≤ algD Γ.M Bs.ψ Bs.emb)
    (hUt : ∀ t : ℝ, ∀ x ∈ U, om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) x ∈ U)
    {ΦD : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} (hΦD : ΦD ∈ U) {Φ Φ₁ : WO W X → ℂ}
    (h0 : IsDatum Γ.M ψ cA ΦD Φ)
    (h1 : IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y 1), 1) ΦD) Φ₁) : p Φ₁ = p Φ := by
  classical
  have huniq : ∀ {x : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} {f g : WO W X → ℂ},
      IsDatum Γ.M ψ cA x f → IsDatum Γ.M ψ cA x g → f = g := fun hf hg =>
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cA.surjective hf hg
  let G : Submodule ℂ (((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) × (WO W X → ℂ)) :=
    { carrier := {q | q.1 ∈ U ∧ IsDatum Γ.M ψ cA q.1 q.2}
      add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ ha.2 hb.2⟩
      zero_mem' := ⟨U.zero_mem, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
      smul_mem' := fun c _ ha => ⟨U.smul_mem c ha.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c ha.2⟩ }
  let fG : G →ₗ[ℂ] U := ((LinearMap.fst ℂ _ _).comp G.subtype).codRestrict U (fun q => q.2.1)
  have hfG : Function.Injective fG := by
    intro q q' hq
    have e1 : q.1.1 = q'.1.1 := congrArg Subtype.val hq
    have e2 : q.1.2 = q'.1.2 := huniq q.2.2 (e1 ▸ q'.2.2)
    exact Subtype.ext (Prod.ext e1 e2)
  haveI : FiniteDimensional ℂ G := Module.Finite.of_injective fG hfG
  let Uf : Submodule ℂ (WO W X → ℂ) := G.map (LinearMap.snd ℂ _ _)
  let Φt : ℝ → WO W X → ℂ := fun t => ωA (oneP θ W τ Y t, 1) Φ
  have hdat : ∀ t, IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) ΦD) (Φt t) := by
    intro t
    have h := hO.weilA ΦD Φ h0 (oneP θ W τ Y t) 1
    rwa [kapX_one] at h
  have hmemU : ∀ t, Φt t ∈ Uf := fun t => ⟨(_, Φt t), ⟨hUt t ΦD hΦD, hdat t⟩, rfl⟩
  have halg : ∀ t, Φt t ∈ algF ψ θ true A B := by
    intro t
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' _ (hU (hUt t ΦD hΦD))
    rwa [huniq hD' (hdat t)] at hΦ'
  have hshift : ∀ s t, ωA (oneP θ W τ Y s, 1) (Φt t) = Φt (s + t) := by
    intro s t
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hY s t, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hzero : ∀ t, ∀ l : Module.Dual ℂ Pi, HasDerivAt (fun s => l (p (Φt s))) 0 t := by
    intro t l
    obtain ⟨Φ', hΦ', hder⟩ := hmap.stabM.2 τ Y hY (Φt t) (halg t)
    have hp := hmap.invl τ Y hY (Φt t) (halg t) Φ' hΦ' hder
    have hd : ∀ z, HasDerivAt (fun s => Φt s z) (Φ' z) t := by
      intro z
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hder z)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show Φt s z = ωA (oneP θ W τ Y (s - t), 1) (Φt t) z
      rw [hshift, sub_add_cancel]
    have h := hasDerivAt_linear (Uf ⊔ Submodule.span ℂ {Φ'}) (l.comp p) (u := Φt)
      (fun s => Submodule.mem_sup_left (hmemU s)) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) hd
    simpa [hp] using h
  have hconst : ∀ l : Module.Dual ℂ Pi, l (p (Φt 1)) = l (p (Φt 0)) := fun l =>
    is_const_of_deriv_eq_zero (fun t => (hzero t l).differentiableAt) (fun t => (hzero t l).deriv) 1 0
  have e1 : Φt 1 = Φ₁ := huniq (hdat 1) h1
  have e0 : Φt 0 = Φ := by
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, Prod.mk_one_one, map_one, Module.End.one_apply]
  rw [← e1, ← e0, ← sub_eq_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by rw [map_sub, hconst l, sub_self]

end GlobalTheory.KInvData
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

section BargmannUnique

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem bk_smul_left (c : ι → ℝ) (u : ℂ) (z₀ z : VCx ι a b) : bk c (u • z₀) z = u * bk c z₀ z := by
  unfold bk
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem conjMono_add (m m' : DVar ι a b →₀ ℕ) (z : VCx ι a b) :
    conjMono (m + m') z = conjMono m z * conjMono m' z := by
  unfold conjMono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem conjMono_single_one (k : DVar ι a b) (z : VCx ι a b) :
    conjMono (Finsupp.single k 1) z = conj (z k.1 k.2.1 k.2.2) := by
  unfold conjMono; simp [Finsupp.prod_single_index]

abbrev monoSpan (ι : Type) [Fintype ι] (a b : ℕ) : Submodule ℂ (VCx ι a b → ℂ) :=
  Submodule.span ℂ (Set.range fun m : DVar ι a b →₀ ℕ => conjMono m)

theorem monoSpan_mul {P Q : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) (hQ : Q ∈ monoSpan ι a b) :
    P * Q ∈ monoSpan ι a b := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
  exact ⟨m + m', funext fun z => conjMono_add m m' z⟩

theorem bk_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) : (fun z => bk c z₀ z) ∈ monoSpan ι a b := by
  have : (fun z => bk c z₀ z) = ∑ τ, ∑ i, ∑ j,
      ((c τ : ℂ) * z₀ τ i j) • conjMono (Finsupp.single (τ, i, j) 1) := by
    funext z
    simp only [bk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conjMono_single_one]
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem bk_pow_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) (n : ℕ) :
    (fun z => bk c z₀ z ^ n) ∈ monoSpan ι a b := by
  induction n with
  | zero =>
    have : (fun z : VCx ι a b => bk c z₀ z ^ 0) = conjMono 0 := by funext z; simp [conjMono]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := monoSpan_mul ih (bk_mem_monoSpan c z₀)
    convert this using 1
    funext z; simp [pow_succ]

theorem exp_norm_le_four (w : ℂ) : Real.exp ‖w‖ ≤ Real.exp ((1 - Complex.I) * w).re +
    Real.exp ((1 + Complex.I) * w).re + Real.exp ((-1 - Complex.I) * w).re + Real.exp ((-1 + Complex.I) * w).re := by
  have h1 : ((1 - Complex.I) * w).re = w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h2 : ((1 + Complex.I) * w).re = w.re + -w.im := by simp [Complex.mul_re] <;> ring
  have h3 : ((-1 - Complex.I) * w).re = -w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h4 : ((-1 + Complex.I) * w).re = -w.re + -w.im := by simp [Complex.mul_re] <;> ring
  rw [h1, h2, h3, h4]
  have key : Real.exp ‖w‖ ≤ Real.exp |w.re| * Real.exp |w.im| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (Complex.norm_le_abs_re_add_abs_im w)
  have hre : Real.exp |w.re| ≤ Real.exp w.re + Real.exp (-w.re) := by
    rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.re, Real.exp_pos (-w.re)]
  have him : Real.exp |w.im| ≤ Real.exp w.im + Real.exp (-w.im) := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.im, Real.exp_pos (-w.im)]
  calc Real.exp ‖w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) * (Real.exp w.im + Real.exp (-w.im)) :=
        key.trans (mul_le_mul hre him (by positivity) (by positivity))
    _ = _ := by simp only [add_mul, mul_add, ← Real.exp_add]; ring

theorem integral_moment_span_eq_zero {c : ι → ℝ} (hc : ∀ τ, 0 < c τ) {F : VCx ι a b → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M)
    (hmom : ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0)
    {P : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) :
    Integrable (fun z => P z * (Real.exp (-gq c z / 2) : ℂ) * F z) ∧
      ∫ z, P z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).1 m).mul_bdd hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM), hmom m⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (fun z => (x + y) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => x z * (Real.exp (-gq c z / 2) : ℂ) * F z + y z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    have e : (fun z => (r • x) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => r * (x z * (Real.exp (-gq c z / 2) : ℂ) * F z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hx.1.const_mul r, by rw [integral_const_mul, hx.2, mul_zero]⟩

theorem integral_bargmann_eq_zero_of_moments : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  intro ι _ a b c hc F hF hMex hmom z₀
  obtain ⟨M, hM⟩ := hMex
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hgq : Continuous (fun z : VCx ι a b => gq c z) := by unfold gq; fun_prop
  have hbk : Continuous (fun z : VCx ι a b => bk c z₀ z) := by unfold bk; fun_prop
  have hg : Continuous (fun z : VCx ι a b => ((Real.exp (-gq c z / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hgq.neg.div_const 2))
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (f := fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (fun n z => ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M))
    (fun n => ((((hbk.pow n).div_const _).mul hg).mul hF).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc]
      gcongr
      exact hM z)
    (Filter.Eventually.of_forall fun z => (hexpR ‖bk c z₀ z‖).summable.mul_right _)
    (by
      have htsum : (fun z => ∑' n : ℕ, ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M)) =
          fun z => Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M) := by
        funext z; rw [tsum_mul_right, (hexpR _).tsum_eq]
      rw [htsum]
      have hI : ∀ u : ℂ, Integrable fun z : VCx ι a b =>
          ‖Complex.exp (bk c (u • z₀) z) * (Real.exp (-gq c z / 2) : ℂ)‖ :=
        fun u => ((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).2 (u • z₀)).norm
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      refine Integrable.mono' ((((hI (1 - Complex.I)).add (hI (1 + Complex.I))).add
        (hI (-1 - Complex.I))).add (hI (-1 + Complex.I)) |>.const_mul M)
        ((Real.continuous_exp.comp (continuous_norm.comp hbk)).mul
          ((Real.continuous_exp.comp (hgq.neg.div_const 2)).mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, bk_smul_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by positivity)]
      have h4 := exp_norm_le_four (bk c z₀ z)
      have he := Real.exp_pos (-gq c z / 2)
      calc Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M)
          = (M * Real.exp (-gq c z / 2)) * Real.exp ‖bk c z₀ z‖ := by ring
        _ ≤ (M * Real.exp (-gq c z / 2)) * (Real.exp ((1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((1 + Complex.I) * bk c z₀ z).re + Real.exp ((-1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((-1 + Complex.I) * bk c z₀ z).re) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (hexpC (bk c z₀ z)).mul_right ((Real.exp (-gq c z / 2) : ℂ) * F z))
  have h0 : ∀ n : ℕ, ∫ z, bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
    intro n
    have := (integral_moment_span_eq_zero hc hF hM hmom
      (Submodule.smul_mem _ ((Nat.factorial n : ℂ)⁻¹) (bk_pow_mem_monoSpan c z₀ n))).2
    have e : (fun z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => ((Nat.factorial n : ℂ)⁻¹ • fun z => bk c z₀ z ^ n) z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this
  simp only [h0] at hsum
  exact hsum.unique hasSum_zero

end BargmannUnique

end GlobalTheory.FockTransl

end
end
