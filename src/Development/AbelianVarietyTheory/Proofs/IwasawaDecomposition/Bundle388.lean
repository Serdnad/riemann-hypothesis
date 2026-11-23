module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.TwQLat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Formalism.LocalToGlobal.Columns.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle365
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.PointWell

open Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem moeb_one {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : moeb 1 z = z := by
  rw [← fromBlocks_one, moeb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem block_of_moeb_eq {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (τ : X.Ψ) (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) (a b : Fin r)
    (ha : X.p0 ≤ a) (hb : (b : ℕ) < X.p0) : ((mat x τ)⁻¹ * mat x' τ) a b = 0 := by
  have hu := frameCo_isUnit₂₂ X hj hp hx τ
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ = reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  rw [moeb_zero, moeb_zero] at h
  generalize frameCo X hj x τ = f at *
  generalize frameCo X hj x' τ = f' at *
  have h1 : f'.toCols₂ = f * fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) := by
    have h0 := fromBlocks_mul_fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂)
      f.toBlocks₁₁ f.toBlocks₁₂ f.toBlocks₂₁ f.toBlocks₂₂
    rw [fromBlocks_toBlocks] at h0
    refine Eq.trans ?_ h0.symm
    simp only [Matrix.mul_zero, zero_add]
    rw [mul_nonsing_inv_cancel_left _ _ hu, ← Matrix.mul_assoc, h, nonsing_inv_mul_cancel_right _ _ hu']
    ext (a | a) b <;> rfl
  have h2 : (f⁻¹ * f').toCols₂ = fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) :=
    (congrArg (f⁻¹ * ·) h1).trans (nonsing_inv_mul_cancel_left f _ hf)
  have hb' : (b : ℕ) < r - j := hp ▸ hb
  have ha' : (a : ℕ) - (r - j) < j := by have := a.2; omega
  have h3 := congrFun (congrFun h2 (Sum.inl ⟨_, ha'⟩)) ⟨_, hb'⟩
  rw [hN] at h3
  have ea : (idx hj).symm (Sum.inl ⟨_, ha'⟩) = a := Fin.ext (by rw [idx_symm_inl]; simp only; omega)
  have eb : (idx hj).symm (Sum.inr ⟨_, hb'⟩) = b := Fin.ext (by rw [idx_symm_inr])
  simpa [toCols₂, ea, eb] using h3

theorem perFr_mem {A : Type} (S : Submodule ℂ (A → ℂ)) (w : A → Fin r → E) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (τ : E →+* ℂ) (m : ℕ) (hm : τ ∈ X.Ψ → m = r - X.p0) (hm' : τ ∉ X.Ψ → m = X.p0)
    (hS : ∀ i < m, (fun a => perFr X x (w a) τ i) ∈ S) (i : ℕ) (hi : i < m) :
    (fun a => perFr X x' (w a) τ i) ∈ S := by
  have hp := X.p0_le
  by_cases h : τ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨τ, h⟩).det := (hx _).1.isUnit
    have hi' : X.p0 + i < r := by omega
    have key : (∑ b : Fin r, ((mat x' ⟨τ, h⟩)⁻¹ * mat x ⟨τ, h⟩) ⟨_, hi'⟩ b •
        fun a => ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ (w a))) b) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · rw [h2 _ _ _ (Nat.le_add_right _ _) hb, zero_smul]; exact zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hbr := b.2
        convert hS (b - X.p0) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_left h, dite_eq_left (by omega)]
        congr 1
        exact Fin.ext (by simp; omega)
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_left h, dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨τ, h⟩) (mat x' ⟨τ, h⟩)⁻¹ hd, ← mulVec_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · have hm := hm' h
    have h' : conjEmb τ ∈ X.Ψ := by_contra fun h' => h ((X.cmType τ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hi' : X.p0 - 1 - i < r := by omega
    have key : (∑ b : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) b ⟨_, hi'⟩ •
        fun a => hermC (conjEmb τ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) b) (Data.emb (conjEmb τ) (w a))) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · refine Submodule.smul_mem _ _ ?_
        convert hS (X.p0 - 1 - b) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_right h, dite_eq_left h', dite_eq_left (by omega)]
        congr 2
        exact Fin.ext (by simp; omega)
      · rw [h1 _ _ _ (not_lt.1 hb) (by simp only; omega), zero_smul]; exact zero_mem _
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_right h, dite_eq_left h', dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
    generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (f := fun b c => ∑ d, n b _ * _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ r}

theorem pt_eq_of_block (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) (x x' : (U.X k).dom)
    (h1 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) :
    (U.un k x).x = (U.un k x').x := by
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', -⟩ := hF k x'
  have hmem : ∀ j, (fun a => P' a j) ∈ Submodule.span ℂ (Set.range fun (j : Fin g) a => P a j) := by
    intro j
    simp only [hP']
    refine perFr_mem (U.X k) _ (fun a => (φ k a : Fin r → E)) x.2 h1 h2 _ (Dw.mult (e j).1) (fun h => ?_)
      (fun h => ?_) (fun i hi => ?_) _ (e j).2.2
    · exact (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega)
    · exact (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm
    · refine Submodule.subset_span ⟨e.symm ⟨(e j).1, ⟨i, hi⟩⟩, funext fun a => ?_⟩
      dsimp only
      rw [hP, Equiv.apply_symm_apply]
  choose μ hμ using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem j)
  have hL : ∀ a, P' a = mulVecLin (of μ) (P a) := fun a => funext fun j => by
    have := congrFun (hμ j) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hsurj : Function.Surjective (mulVecLin (of μ)) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (mulVecLin (of μ))).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  rw [hx, hx']
  exact (F.fibre _ P P' hper hper').2 ⟨LinearEquiv.refl _ _,
    LinearEquiv.ofBijective _ ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun _ _ => rfl,
    fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hL⟩

end GlobalTheory.TrueCx.PointWell
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DnFv

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj
open Formalism.HermitianLatticesTheory (localization₂ dual)

theorem dual_map_smul {F V : Type} {iF : CommSemiring F} {iV : AddCommMonoid V} {iM : Module F V} (φ : Module.Dual F V) (a : F) (y : V) :
    φ (a • y) = a * φ y := by
  rw [map_smul, smul_eq_mul]

section TD

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem dn_extF_ok (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    ((A.deco c.1 (S.rep c)).dn P (TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g)).Ok := by
  have hN := ht.dnN_eq c.1 (S.rep c) P
  refine (ht.ok c.1 (S.rep c)).dn P hM ?_ ?_ ?_ ?_
  · intro x hx y hy
    rw [← hN] at hx hy
    rw [extF_of_mem g hx, extF_of_mem g hy, extF_of_mem g ((localization₂ _ _).add_mem hx hy), redL_add hx hy, map_add (f := _)]
  · intro r x hx
    rw [← hN] at hx
    rw [extF_of_mem g hx, extF_of_mem g ((localization₂ _ _).smul_mem r hx), redL_osmul r hx, map_smul]
    rfl
  · intro x hx
    rw [← hN] at hx
    exact extF_of_notMem g hx
  · obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
      by_contra H
      push Not at H
      exact hg (LinearMap.ext H)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x.1, hN ▸ x.2, ?_⟩
    rw [extF_of_mem g (le_locP _ _ x.2), redL_coe]
    exact hz

theorem N_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.N c.1 (A.dnPt P c g) = A.dnN c.1 (S.rep c) P := by
  have h := congrArg Deco.N (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  exact h.trans (ht.dnN_eq c.1 (S.rep c) P).symm

theorem f_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.f c.1 (A.dnPt P c g) P = TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g := by
  classical
  have h := congrArg (fun d => Deco.f d P) (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  refine h.trans ?_
  simp [Deco.dn]

theorem fv_dn (ho : A.Ok T) (ht : A.Tied T) (hl : A.Laws T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) {x : Fin n → E} {s : 𝓞 E} {G : Matrix (Fin n) (Fin n) E}
    (hG : G = (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E))
    (hsx : s • x ∈ A.N (S.cl c.1 (A.dnPt P c g)).1 (S.rep (S.cl c.1 (A.dnPt P c g)))) :
    ∃ h : s • (G *ᵥ x) ∈ A.dnN c.1 (S.rep c) P,
      A.fv P (S.cl c.1 (A.dnPt P c g)) (Submodule.Quotient.mk ⟨_, hsx⟩) = g (Submodule.Quotient.mk ⟨_, h⟩) := by
  subst hG
  have hms : S.mv c.1 (A.dnPt P c g) • S.rep (S.cl c.1 (A.dnPt P c g)) = A.dnPt P c g := S.mv_smul c.1 _
  have e : (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ (s • x) =
      s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
    rw [← algebraMap_smul E s, ← algebraMap_smul E s, Matrix.mulVec_smul]
  have h1 := (ho.N_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) (s • x)).2 hsx
  rw [hms, N_dnPt ht P hM c hg, e] at h1
  refine ⟨h1, ?_⟩
  have h3 := ho.f_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) P (s • x)
  have h4 : redL (A.dnN c.1 (S.rep c) P) P.1 (s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x)) =
      Submodule.Quotient.mk ⟨_, h1⟩ := redL_coe ⟨_, h1⟩
  rw [hms, f_dnPt ht P hM c hg, e, extF_of_mem g (le_locP _ _ h1), h4] at h3
  exact (fv_mk hl P _ ⟨_, hsx⟩).trans h3.symm


omit [NumberField K] [StarRing K] in
theorem exists_smul_mem_N {SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)
    {y : Fin n → E} (hy : y ∈ d.Lsh) : ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.N := by
  have h := le_locP P.1 _ hy
  rw [localization_Lsh_eq_localization_N hd ha P rfl] at h
  exact (mem_locP _ _ _).1 h

end TD

end GlobalTheory.DnFv

end


open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj in
open Formalism.HermitianLatticesTheory (localization₂ dual) in

theorem GlobalTheory.Mem.Col2.TC.dn_level_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ x hx
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, hc⟩ := hc i hi
  have hLc := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hmv := moveHyp_of_ok l.pr u v
  have hM : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hmv.ne, hmv.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hd : ∀ c', (((I.stp u a i).rep c').1.1.deco.1).Ok := fun c' => ((I.stp u a i).rep c').1.1.deco.2
  have hD : ∀ c', LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c')) = (((I.stp u a i).rep c').1.1.deco.1).Lsh := fun c' =>
    (@dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (fun _ => rfl) _ hgr _).trans (congrArg _ (hLc c'))
  have hx2 : (x.1 : Fin (B.R.N i) → B.fields.E) ∈ (((I.stp u a i).rep ((I.fm l u a).dn i v c.1 g)).1.1.deco.1).Lsh :=
    (SetLike.ext_iff.1 (hD _) _).1 x.2
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.DnFv.exists_smul_mem_N (hd _) ha v hx2
  have hγ' : (γ.1.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) = _ := congrArg Units.val hγ
  obtain ⟨h1, h2⟩ := GlobalTheory.DnFv.fv_dn ((l.lev u a).lev i) ((l.lev u a).tied i) ((l.fmL u a).lev i) v hM c.1 hg hγ' hsx
  let s' : 𝓞 (I.rec7 l Z).host.E := s
  have hs' : (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) ≠ 0 := mk_ne_zero hs
  have f1 : ((I.fm l u a).fv i v _ (L.pr v _ (s' • x)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * (I.fm l u a).fv i v _ (L.pr v _ x) :=
    (congrArg ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) (L.pr_smul v _ s' x)).trans
      (GlobalTheory.DnFv.dual_map_smul ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) _ _)
  let z : ↥(LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) := ⟨_, hx⟩
  have f2 : (g (L.prk v c.1 (s' • z)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * g (L.prk v c.1 z) :=
    (congrArg g (L.prk_smul v c.1 s' z)).trans (GlobalTheory.DnFv.dual_map_smul g _ _)
  refine mul_left_cancel₀ hs' (f1.symm.trans (Eq.trans ?_ f2))
  have e1 := hL.1 v _ (s' • x) hsx
  have e2 := hL.2 v c.1 (s' • z) h1
  exact (congrArg _ e1).trans (h2.trans (congrArg g e2.symm))
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryAdelic_twist_diagonal_at_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.Mem.Col2.TwUnit.exists_tw | exact GlobalTheory.Mem.Col2.TwUnit.exists_tw | (intros; apply GlobalTheory.Mem.Col2.TwUnit.exists_tw <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isPtOf_mul_J0_decoration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  exact @GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pointLattice_iff_baseLattice_decorated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  first | exact @GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | exact GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | (intros; apply GlobalTheory.Mem.Col2.PtLat.latS_deco_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.placeProjection_eq_basePi_mul_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  first | exact @GlobalTheory.Mem.Col2.prV_eq_pi_mul | exact GlobalTheory.Mem.Col2.prV_eq_pi_mul | (intros; apply GlobalTheory.Mem.Col2.prV_eq_pi_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdFirst

theorem qPi_eq_phi_of_adAt : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  intro F E K _ _ _ _ _ _ _ hc n _ Q Θ q P hP a e he
  have hw : P.1.under (𝓞 F) = qv F P.1 := HeightOneSpectrum.ext rfl
  set ψ := GlobalTheory.Mem.Dil.psi (qv F P.1) P.1 hw with hψ
  set sp := q.sp P with hsp

  have hu' : ψ (sp.symm (0, 1)) = 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_mem_notMem (Ne.symm hP)
    have hcr : cO E r ∉ P.1.asIdeal := fun h => hr' ((mem_conjP _ _).2 h)
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hcr
    set w := Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) with hwdef
    have hws : w = Formalism.UG.sigR hc.sig _ (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) ((cO E r : 𝓞 E) : E)) := by
      rw [hwdef]
      show _ = Formalism.UG.inclE (F := F) _ (star (star ((r : 𝓞 E) : E)))
      rw [star_star]
    have hw2 : (sp w).2 = q.phi P ((cO E r : 𝓞 E) : E) := by
      rw [hws, hsp, q.sp_sig]
      rfl
    set z := sp.symm (0, ((sp w).2)⁻¹) with hz
    have hzint : z ∈ Formalism.BasicNotions.intV E (qv F P.1) := by
      refine (q.sp_int P z).2 ⟨?_, ?_⟩
      · rw [hz, ← hsp, sp.apply_symm_apply]; exact zero_mem _
      · rw [hz, ← hsp, sp.apply_symm_apply]; show ((sp w).2)⁻¹ ∈ _; rw [hw2]; exact hinv
    have hwz : w * z = sp.symm (0, 1) := by
      apply sp.injective
      rw [map_mul, hz, sp.apply_symm_apply, sp.apply_symm_apply]
      refine Prod.ext (mul_zero _) ?_
      show (sp w).2 * ((sp w).2)⁻¹ = 1
      rw [hw2]
      exact mul_inv_cancel₀ hne
    have hidem : ψ (sp.symm (0, 1)) * ψ (sp.symm (0, 1)) = ψ (sp.symm (0, 1)) := by
      rw [← map_mul, ← map_mul sp.symm]
      simp
    rcases mul_eq_zero.1 (show ψ (sp.symm (0, 1)) * (ψ (sp.symm (0, 1)) - 1) = 0 by rw [mul_sub, hidem, mul_one, sub_self]) with h | h
    · exact h
    · exfalso
      have h1 : ψ (sp.symm (0, 1)) = 1 := sub_eq_zero.1 h
      rw [← hwz, map_mul] at h1
      have hv1 : Valued.v (ψ w) < 1 := by
        rw [hψ, hwdef, GlobalTheory.Mem.Dil.psi_inclE]
        exact GlobalTheory.Mem.Dil.val_lt_one hr
      have hv2 : Valued.v (ψ z) ≤ 1 := (GlobalTheory.Mem.Dil.mem_intV_iff (qv F P.1) z).1 hzint P.1 hw
      have h3 := congrArg Valued.v h1
      rw [map_mul, map_one] at h3
      exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hv2) hv1))
  have hu : ψ (sp.symm (1, 0)) = 1 := by
    have e1 : sp.symm (1, 0) + sp.symm (0, 1) = 1 := by
      rw [← map_add (f := _)]; simp
    have e2 := congrArg ψ e1
    rw [map_add (f := _), hu', add_zero, map_one] at e2
    exact e2

  set x := prV (E := E) (qv F P.1) a - Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) e with hx
  have hψx : ψ x = 0 := by
    rw [hx, map_sub, hψ, GlobalTheory.Mem.Dil.psi_prV, GlobalTheory.Mem.Dil.psi_inclE, he, sub_self]
  have hx1 : (sp x).1 = 0 := by
    by_contra ht
    have hxy : x * sp.symm (((sp x).1)⁻¹, 0) = sp.symm (1, 0) := by
      apply sp.injective
      rw [map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      exact Prod.ext (mul_inv_cancel₀ ht) (mul_zero _)
    have h2 := congrArg ψ hxy
    rw [map_mul, hψx, zero_mul, hu] at h2
    exact zero_ne_one h2
  have e3 : qPi q P a - q.phi P e = (sp x).1 := by
    rw [hx, map_sub]
    rfl
  exact sub_eq_zero.1 (e3.trans hx1)

end GlobalTheory.Mem.Col2.AdFirst
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.diamondElement_integral_support_lastRow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  first | exact @GlobalTheory.Mem.Dil.dia_data | exact GlobalTheory.Mem.Dil.dia_data | (intros; apply GlobalTheory.Mem.Dil.dia_data <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word) (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ → (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | (intros; apply GlobalTheory.Mem.LevTwist.T_notMem_under_uSG <;> assumption)
end
