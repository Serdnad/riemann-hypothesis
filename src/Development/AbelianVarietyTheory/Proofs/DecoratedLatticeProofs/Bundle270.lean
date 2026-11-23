module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalDoubleCosetRepresentativeBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

section Frame

variable {n p q : ℕ} (e : Fin n ≃ Fin p ⊕ Fin q)

theorem submatrix_symm_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e.symm id * Y = (X * Y).submatrix e.symm id := by
  ext i j
  simp [Matrix.mul_apply]

theorem mul_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    B * X.submatrix e.symm id = (B.submatrix e e * X).submatrix e.symm id := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by ext; simp
  conv_lhs => rw [hB]
  rw [show X.submatrix e.symm id = X.submatrix e.symm (Equiv.refl _) from rfl, submatrix_mul_equiv]
  rfl

theorem conj_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (X.submatrix e.symm id)ᴴ * B * X.submatrix e.symm id = Xᴴ * B.submatrix e e * X := by
  rw [Matrix.mul_assoc, mul_submatrix_symm, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, Matrix.mul_assoc]

end Frame

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem sortedFrame_gram (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (sortedFrame M hV τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ = gramAt D V τ := by
  rw [sortedFrame, conj_submatrix_symm, Jpq_submatrix, M.fr_gram τ]

theorem isCartanFrame_sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Cusp.IsCartanFrame V (sortedFrame M hV) :=
  sortedFrame_gram M hV

theorem sortedFrame_cart (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    sortedFrame M hV τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ := by
  rw [sortedFrame, submatrix_symm_mul, mul_submatrix_symm, Jpq_submatrix, cart, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.one_mul]

theorem isCartanInv_cart (M : DSModel V S) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hd := fr_det M τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Formalism.REAL.Jm, diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp
  have hJh : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.REAL.Jm, diagonal_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, diagonal_apply, h, Ne.symm h]
  have hg : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have e : cart M τ = (M.fr τ)⁻¹ * ((M.fr τ)⁻¹)ᴴ * gramAt D V τ := by
    rw [cart, ← M.fr_gram τ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (M.fr τ)⁻¹ ((M.fr τ)⁻¹)ᴴ (M.fr τ)ᴴ, h1, Matrix.mul_one]
  rw [e]
  exact GlobalTheory.Doubling.isCartanInv_of_frame (Matrix.nonsing_inv_mul _ hd) hg hJ hJh

theorem exists_maj_cart (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) :
    ∃ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a ∧
      ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨a, ha, -, hs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ (fun τ => isCartanInv_cart M τ)
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D V τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D V τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

theorem exists_kStable (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊥, inferInstance, zero_mem _, fun g _ v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    obtain ⟨W', h1', h2', h3'⟩ := hy
    refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup h2 h2', fun g hg v hv => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg y hy) (h3' g hg z hz)
  | smul a x _ hx =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    exact ⟨W, h1, W.smul_mem a h2, h3⟩

theorem isKFinite_value (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf θ V (sortedFrame M hV)) (T v) := by
  choose W hWf hvW hWK using fun τ => exists_kStable M τ (hv τ)
  let W' : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => (W τ).comap (M.sm τ).subtype
  have hW' : ∀ τ, FiniteDimensional ℂ (W' τ) := fun τ => by
    haveI := hWf τ
    refine Module.Finite.of_injective (LinearMap.codRestrict (W τ) ((M.sm τ).subtype.comp (W' τ).subtype)
      fun x => x.2) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W τ => (z : M.H τ)) h))
  have hfd := GlobalTheory.T.finiteDimensional_span_multilinear_values' (fun τ => M.sm τ) (GA D V → ℂ) T W' hW'
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfd, fun k hk => ?_⟩
  obtain ⟨v', hv', hx⟩ := GlobalTheory.T.multiplicity_map_right_translate_real_point D θ hθ V S M J χ T hT k (GlobalTheory.Cusp.Kinf_le hk) v
  have e : (fun g => T v (g * k)) = T v' := funext hx
  rw [e]
  refine Submodule.subset_span ⟨v', fun τ => ?_, rfl⟩
  show ((v' τ : M.sm τ) : M.H τ) ∈ W τ
  rw [hv' τ]
  exact hWK τ _ (GlobalTheory.T.maximal_compact_sorted_frame_acts_through_model_compact D θ V S M hV k hθ hk τ) _ (hvW τ)

theorem conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} (F : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hF : F ∈ MultT θ M J χ) (w : SmT M)
    (hw : w ∈ Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v}) :
    (fun g => conj (F w g)) ∈ GlobalTheory.Cusp.A0 θ V (sortedFrame M hV) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 hF)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    have e : F (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm F v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    have ha := hT.aut v
    refine GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ V _ ha,
      (GlobalTheory.Cusp.conj_mem_cuspCont ⟨ha.cont, ha.left, hT.cusp v⟩).2.2⟩, ?_⟩
    exact GlobalTheory.Mem.AutConj.finiteDimensional_span_star (isKFinite_value θ hθ M hV hT v hv)
      (by rintro f ⟨k, hk, rfl⟩; exact ⟨k, hk, funext fun g => by simp⟩)
  | zero =>
    convert zero_mem (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)) using 1
    funext g; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext g; simp
  | smul a x _ hx =>
    convert (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)).smul_mem (conj a) hx using 1
    funext g; simp

end GlobalTheory.ChainOnto.RealData

open GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨RealData.sortedFrame s.M hs.sigOK, a, RealData.isCartanFrame_sortedFrame _ _, fun τ => RealData.isCartanInv_cart _ τ,
    fun τ => RealData.sortedFrame_cart _ _ τ, ha, hmaj, fun u v hv => RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_hecke_of_mem_partFull {D : D7} {c : Com D} {s : PiLocalization₂ D} (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hu : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D s.V))
    (hR : Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R) (v : SmT s.M) :
    heckeLin s.V R (PiLocalization₂.val u v) = e P d • PiLocalization₂.val u v := by
  have h := ((mem_partFull c.θ s.M _ _ c.S e _).1 hu).2 P d R hR
  have key : heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = e P d • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    apply PiTensorProduct.ext
    ext x
    have := h x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at this ⊢
    convert congrFun this _ using 2 <;> simp [PiTensorProduct.lift_symm]
  exact congrFun (congrArg DFunLike.coe key) v |>.trans rfl

theorem partPar : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e →
    (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  intro hP D c hc j hj s hs u e hu
  obtain ⟨hval, hHk, hconj⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hP D c hc j hj s hs
  obtain ⟨-, hlat⟩ := GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs
  obtain ⟨-, hsph, -⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hlev : ∀ v, ∀ k ∈ levS s.V s.β s.L, ∀ g, (fun g => conj (PiLocalization₂.val u v g)) (g * k) =
      (fun k => conj (Lev.levChi s.V s.β s.L k)) k * (fun g => conj (PiLocalization₂.val u v g)) g := by
    intro v k hk g
    simp only [(hval u v).2.2.2 k hk g, map_mul]
  have hhk : ∀ v P d R, Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R →
      heckeLin s.V R (fun g => conj (PiLocalization₂.val u v g)) = (fun P d => conj (e P d)) P d • (fun g => conj (PiLocalization₂.val u v g)) := by
    intro v P d R hR
    rw [hconj, val_hecke_of_mem_partFull u e hu P d R ((hHk P d R).2 hR) v]
    funext g
    simp [map_mul]
  have hne : ∀ v, PiLocalization₂.val u v ≠ 0 → (fun g => conj (PiLocalization₂.val u v g)) ≠ 0 := by
    intro v h0 h
    apply h0
    funext g
    simpa using congrFun h g
  have hiff : ∀ v B, PiLocalization₂.val u v ≠ 0 →
      (ParFun c s (PiLocalization₂.val u v) B ↔ GlobalTheory.LFun.IsSysParamD D c.S s.V.rank (fun P d => conj (e P d)) B) := by
    intro v B h0
    unfold ParFun
    rw [hlat]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph (hne v h0) (hlev v) (hhk v) B
  have second : ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
    intro w B hw hB
    refine ⟨?_, fun v hv => (hiff v B hv).2 ((hiff w B hw).1 hB)⟩
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun hu0 => ?_, second⟩
  have hu1 : (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu1 (LinearMap.ext hh)
  obtain ⟨C, hC⟩ := (hval u v).2.1
  have hbdd : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj.comp (hval u v).1), fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [(hval u v).2.2.1 γ hγ g]
    · simpa using hC g
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph
    _ hbdd (hne v hv) (hlev v) (fun P d => conj (e P d)) (hhk v)
  have hpf : ParFun c s (PiLocalization₂.val u v) B := by
    unfold ParFun
    rw [hlat]
    exact hB
  exact ⟨B, second v B hv hpf⟩

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  first | exact @GlobalTheory.OntoDecomp.multT_span_partFull | exact GlobalTheory.OntoDecomp.multT_span_partFull | (intros; apply GlobalTheory.OntoDecomp.multT_span_partFull <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  first | exact @GlobalTheory.ChainMetric.metEx | exact GlobalTheory.ChainMetric.metEx | (intros; apply GlobalTheory.ChainMetric.metEx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  first | exact @GlobalTheory.LastBiTheta.isBiTheta_lastBi | exact GlobalTheory.LastBiTheta.isBiTheta_lastBi | (intros; apply GlobalTheory.LastBiTheta.isBiTheta_lastBi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_contraction_extendByZero_double_combination : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), (∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn (fun w => f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ) → ∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂) := by
  first | exact @GlobalTheory.ContrComb.contr_comb_ext | exact GlobalTheory.ContrComb.contr_comb_ext | (intros; apply GlobalTheory.ContrComb.contr_comb_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_source_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extS_slice | exact GlobalTheory.FinPl.ExtZero.comb_extS_slice | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extS_slice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_target_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | exact GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  first | exact @GlobalTheory.DisjComb.main | exact GlobalTheory.DisjComb.main | (intros; apply GlobalTheory.DisjComb.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.exists_rational_double_coset_representative_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g → (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1 + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) → ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 → ∃ γ : AutY X R (j + 1), (∃ g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, IsGL ι γ g' ∧ DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g' = DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h') ∧ (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  first | exact @GlobalTheory.TwBridge.repsOnto | exact GlobalTheory.TwBridge.repsOnto | (intros; apply GlobalTheory.TwBridge.repsOnto <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.completion_representative_mem_previous_index_set : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
  first | exact @GlobalTheory.RepsAtTwist.exists_rep_flat_ne | exact GlobalTheory.RepsAtTwist.exists_rep_flat_ne | (intros; apply GlobalTheory.RepsAtTwist.exists_rep_flat_ne <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistPrime_parahoricEntries_eq_columnData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.EntryAtTwist.entryAgree | exact GlobalTheory.EntryAtTwist.entryAgree | (intros; apply GlobalTheory.EntryAtTwist.entryAgree <;> assumption)
end
