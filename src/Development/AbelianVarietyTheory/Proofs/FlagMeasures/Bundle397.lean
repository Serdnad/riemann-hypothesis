module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle387
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle016

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFamCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem scalar_of_same_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 ∧ (Y.tO u u').scal t t' := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsLattice D.host.E t.lam := hrow.2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh : Th t.lam (lf D (X.Fu u)) t.frame t'.frame (n * (t.lin * n' * t.lin⁻¹)) = Hp t.lam (lf D (X.Fu u)) t.frame := by
    first
    | exact GlobalTheory.T.theta_cocycle_product_of_rational_unipotents D t.lam (lf D (X.Fu u)) t.frame t'.frame hrow.1.1 rfl hLt.2 hLt'.2 n hn1 _ hm hfr
    | exact GlobalTheory.T.theta_cocycle_product_of_rational_unipotents D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  have hsc := GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh hsc
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hrow.1.1 _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  refine ⟨?_, ?_⟩
  · show s0T t t' = 1
    unfold s0T
    rw [if_pos ⟨hlam, hlam'⟩]
    exact hs0
  · show scalT t t'
    exact ⟨⟨hlam, hlam'⟩, hs0, hsc⟩

end GlobalTheory.SnFamCoset
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ArchGramFibre

open Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation PI.VolStabS

theorem exists_real_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y := by
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩

theorem gramB_surj_of_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
      ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S := by
  intro X hX S
  have := semisimpleTens_holds F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E :=
    fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)

      simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add (f := _)]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

theorem exists_submersion_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
      (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
        gramR (Ainf F) σ J X) ∧
      ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X)) := by
  obtain ⟨n, m, eV, eH, hV, hH⟩ := exists_real_coords F E σ hCM M a
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, PI.VolStabS.hR_add_left, PI.VolStabS.hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := quadCoord_holds _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := gramB_surj_of_free F E σ hCM M a J hJ X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem gram_densities (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Ainf F) σ J) Subtype.val ν {X | LinearIndependent (Ainf F ⊗[F] E) X} := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ := exists_submersion_coords F E σ hCM M a J hJ
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := submDens_holds n m _ _ hμ' hν' f' hC
  refine densAll_transport μ ν (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

theorem exists_fibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  intro F E _ _ _ _ _ σ hCM M a J hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_of_tens PI.VolStabS.DiscreteGroups.fibOfDens_holds
    (tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)) μ ν hμ hν
    (gram_densities F E σ hCM M a J hJ μ ν hμ hν)

end GlobalTheory.ArchGramFibre
end
end
