module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle172
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem sum_pullMat_subBG_reframe : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  intro D p _ X E pos fd lam ι hι ρ hL e c j La La' he he' hdet x y
  classical
  have hs : ∀ q : D.host.E, star q = D.host.conj q := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hcc : ∀ q : D.host.E, D.host.conj (D.host.conj q) = q := fun q => D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
  have hconj : ∀ τ q, TaylorLogMetric.embT D τ (D.host.conj q) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ q) := fun τ q =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) q
  have hιe : ∀ τ q, ι (TaylorLogMetric.embT D τ q) = twG X E (pos.symm τ).1 (pos.symm τ).2
      (ρ _ (if IsOddPos (pos.symm τ).2 then D.host.conj q else q)) := by
    intro τ q
    have halg : TaylorLogMetric.embT D τ q ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) q).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
    have h2 := hL (pos.symm τ).1 (pos.symm τ).2 q
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h2
    rw [← h2]; unfold TaylorLogMetric.lamC; rw [dite_eq_left halg]; exact hι ⟨_, halg⟩
  have hinv : ∀ {n : ℕ} (v : X.Pl) (A : Matrix (Fin n) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin n) (X.G.P.Qq v)),
      A * star A = 1 → ((star A).map (ρ v) * M)⁻¹ = M⁻¹ * A.map (ρ v) := by
    intro n v A M h
    rw [Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero (ρ v)) (map_one (ρ v))]
  obtain ⟨τ, b0, a0⟩ := x
  obtain ⟨τ', b1, a1⟩ := y
  by_cases hxy : τ = τ'
  · subst hxy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [subBG, reframe, pullMat, ↓reduceIte]
      rw [hinv _ _ _ he, hinv _ _ _ he']
      by_cases hodd : IsOddPos (pos.symm τ).2

      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
        Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
        Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · intro τ'' _ hne
      apply Finset.sum_eq_zero
      intro z _
      simp [pullMat, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [show subBG E pos (reframe fd ρ e) j La La' (τ, b0, a0) (τ', b1, a1) = 0 from if_neg hxy, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : τ = z.1
    · have h2 : z.1 ≠ τ' := fun h => hxy (h1.trans h)
      rw [show subBG E pos fd j La La' z (τ', b1, a1) = 0 from if_neg h2, mul_zero, mul_zero]
    · rw [show pullMat (e j La) (e (j + 1) La') (τ, b0, a0) z = 0 from if_neg h1, map_zero, zero_mul]

end GlobalTheory.TwV.DelB
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem xiM_eq_adelic : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' z = S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe hr hr' z)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj hr hr' La La' z
  have h : j + 1 ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j ∧ ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := ⟨hj, hr, hr'⟩
  have hz : Formalism.L2.Col.inFr ((J.fd std).trG j La).symm ((J.fd std).trG (j + 1) La').symm
      (Formalism.L2.Col.inFr ((J.fd std).trG j La) ((J.fd std).trG (j + 1) La') z) = z := by
    unfold Formalism.L2.Col.inFr
    ext x
    simp
  show Formalism.L2.PairingIndexBounds.F.movD _ _ _ z = _
  unfold Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left h, hz]

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]



theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dite_eq_left ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SerMap

theorem iteratedFDeriv_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => c * G z) α = c * TaylorLogMetric.taylor D G α := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    unfold TaylorLogMetric.taylor
    simp
  · unfold TaylorLogMetric.taylor
    have h := iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)
    simp only [smul_eq_mul] at h
    rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem padicSeries_const_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]),
    (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar →
    TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) →
    serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  intro D p _ lam ι hι a b K G s s' hs hK hKG
  ext α
  have hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α := by
    have : K = fun z => s' * G z := funext hKG
    rw [this, taylor_mul]
  have hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs (hK α)
  show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _
  rw [taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem, ← hι ⟨_, hmem⟩]
  show ι (s * TaylorLogMetric.taylor D K α) = _
  rw [hKt, ← mul_assoc, map_mul]
  rfl

end GlobalTheory.TwV.SerMap
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem taylor_reV {D : D7} {a b N N' : ℕ} (ha : a = N) (hb : b = N') (G : TaylorLogMetric.VC D N N' → ℂ)
    (α : GL3Theta.Idx D N N' →₀ ℕ) :
    TaylorLogMetric.taylor D (reV ha hb G) (α.mapDomain fun k => (k.1, Fin.cast hb.symm k.2.1, Fin.cast ha.symm k.2.2)) =
      TaylorLogMetric.taylor D G α := by
  subst ha hb
  have h1 : reV (D := D) rfl rfl G = G := by funext z; rfl
  have h2 : (fun k : GL3Theta.Idx D a b => (k.1, Fin.cast (rfl : b = b).symm k.2.1, Fin.cast (rfl : a = a).symm k.2.2)) = id := by
    funext k; rfl
  rw [h1, h2, Finsupp.mapDomain_id]

theorem coeff_resV_thCl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) {K : Type} [Field K] (ι : ℂ →+* K) (j : ℕ) (hN : RankTie X D j) (La : X.Lt j) (La' : X.Lt (j + 1)) (s : K) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ), MvPowerSeries.coeff (α.mapDomain (eIdx X D pos j hN)) (resV (kapOf X pos j) (s • MvPowerSeries.map ι (tay (thCl t u μ cls j La La')))) = s * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2)) α) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X pos cls K _ ι j hN La La' s α
  have hr : (X.Pj j).m + 1 = D.R.N j ∧ (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) :=
    ⟨(Formalism.L2.G.Pend.rank_eq X j).trans hN.1.symm, (Formalism.L2.G.Pend.rank_eq X (j + 1)).trans hN.2.symm⟩
  have hres : ∀ {ι' κ' : Type} (f : κ' → ι') (Th : MvPowerSeries ι' K) (n : κ' →₀ ℕ),
      MvPowerSeries.coeff n (resV f Th) = MvPowerSeries.coeff (n.mapDomain f) Th := fun _ _ _ => rfl
  have hcomp : (Formalism.L2.G.Pend.kapOf X pos j ∘ eIdx X D pos j hN) =
      fun k => (k.1, Fin.cast hr.2.symm k.2.1, Fin.cast hr.1.symm k.2.2) := by
    funext k
    simp only [Function.comp, Formalism.L2.G.Pend.kapOf, eIdx, Sigma.eta, Equiv.apply_symm_apply]
    ext <;> rfl
  rw [hres, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hcomp]
  congr 2
  show TaylorLogMetric.taylor D (thCl t u μ cls j La La') _ = _
  rw [thCl, dite_eq_left hr]
  exact taylor_reV hr.1 hr.2 _ α

end GlobalTheory.TwV.DelB
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem gl_one_eq_of_det_eq {R : Type*} [CommRing R] (g h : GL (Fin 1) R)
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : (g : Matrix (Fin 1) (Fin 1) R).det = (h : Matrix (Fin 1) (Fin 1) R).det := by
    have := congrArg Units.val e
    simpa using this
  ext i k
  rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
  simpa [Matrix.det_unique] using e'

theorem siteD_inTw_charts_tw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt Hh St hv hZ
  obtain ⟨Fo, fin, S⟩ := Z
  dsimp only at hZ
  subst hZ
  refine ⟨fun j hj => rfl, ?_⟩
  intro j hj β x y hy
  have hyx : y = detU D (j + 1) hj x := by
    apply Subtype.ext
    apply gl_one_eq_of_det_eq
    rw [det_detU]
    exact hy
  subst hyx
  rfl

end GlobalTheory.Port
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem chart_eq_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c La Lb hLa hLb
  unfold Joint.chart
  rcases j with _ | j
  · haveI := J.ch0
    exact Subsingleton.elim _ _
  · simp only
    rw [Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c La, Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c Lb]
    have ea := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c La hLa
    have eb := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c Lb hLb
    have key : ∀ (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (h : (I.at' j hj).C = C) (St' : GlobalTheory.TwU.StepCharts C (j + 1) hj)
        (_ : St' = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st)) (x y : (I.at' j hj).C.cls (j + 1)),
        (I.at' j hj).st.chOf x = (I.at' j hj).st.chOf y →
        St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) x) = St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) y) := by
      intro C h St' hst x y e
      subst h
      subst hst
      exact e
    exact key _ (X.onCh j hj) _ (J.st j hj) _ _ (ea.trans eb.symm)

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem dec_exists : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → Nonempty (Dec J std)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  classical
  refine ⟨{ gam := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then Classical.choose (hD j hj La h).2.1 else 1,
            kap := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then
              Classical.choose (Classical.choose_spec (hD j hj La h).2.1).2 else 1,
            mem := ?_, eq := ?_ }⟩
  · intro j hj La
    by_cases h : ((sysS H X std).Pj j).IsLatTup La.2
    · rw [dif_pos h]
      exact (Classical.choose_spec (hD j hj La h).2.1).1
    · rw [dite_eq_right h]
      exact Subgroup.one_mem _
  · intro j hj La h
    simp only [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hD j hj La h).2.1).2

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LbB

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem splAlg_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a



theorem lbAtB_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (hrat : FrRatJ t B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
    (hL : L = reL (rankN D (i + 1) hi) Lb) : GlobalTheory.TwV.LbAtB (locJ hi t B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locJ hi t B) (splAlg_locJ hi t B) _
    (frAtB_re (rankN D (i + 1) hi) (locJ hi t B) Lb B rfl (fun v => t.fr _ ((X.g u w hg).pl v).2)
      (fun v tt => t.fr_lat _ _ tt) (fun v => hrat _ _))

end Step

theorem lbAtB_inTw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  intro D X0 u w hg Tw μ Z Fl ht Gt j hj β

  exact lbAtB_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B (Z.frRat Fl ht j hj β) _
   (reL_symm (rankN D (j + 1) hj) _).symm

end GlobalTheory.TwV.LbB

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pull_eq_linear (D : D7) (T : TaylorLogMetric.Tor D) (hT : ∀ τ, T.emb τ = TaylorLogMetric.embT D τ) {a b : ℕ}
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.pull D T e e' Θ = fun z => Θ (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin b × Fin a, pullMat e e' (τ, i, j) x * z x.1 x.2.1 x.2.2) := by
  funext z
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT,
    Fintype.sum_prod_type, pullMat]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.star_def]
  ring

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem tay_eq_taylorDir (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) :
    tay G = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
  ext α
  exact GlobalTheory.ConjSeries.taylor_eq_coeff D G α

theorem tay_pull_linSub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  intro D cc δ a b e e' Θ hΘ
  rw [pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]
  exact GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ

end GlobalTheory.TwV.DelB
end
