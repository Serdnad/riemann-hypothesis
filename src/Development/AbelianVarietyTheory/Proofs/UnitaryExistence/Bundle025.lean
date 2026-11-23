module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frMapUniq_scal_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x (1 : S) i = 1 := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun
  simp only [map_one]

theorem frMapUniq_chart_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem frMapUniq_refl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  apply GlobalTheory.FramedBaseChange.refl <;> assumption

theorem frMap_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  refine ⟨?_, frMapUniq_refl y, fun z => ?_⟩
  · rintro ⟨x, xo, u, t, e, b, s, g⟩ ⟨x', xo', u', t', e', b', s', g'⟩ ⟨hx, hu, pm, hs, hf, ha⟩
      ⟨hx', hu', pm', hs', hf', ha'⟩
    dsimp only at hx hu hx' hu' pm pm' hs hf ha hs' hf' ha'
    have h1 : x = x' := hx.trans hx'.symm
    subst h1
    have h2 : u = u' := by
      funext τ i
      exact (hu τ i).trans (hu' τ i).symm
    subst h2
    have h3 : pm = pm' := by
      apply pullback.hom_ext
      · exact hf.trans hf'.symm
      · exact hs.trans hs'.symm
    subst h3
    have h4 : s = s' := by
      have : s.f = s'.f := by
        funext i
        have h := frMapUniq_chart_le pm hs i
        exact (ha i h).symm.trans (ha' i h)
      cases s; cases s'
      congr
    subst h4
    rfl
  · have k : ∀ i : (PPx y.x).ι, scal y.x (1 : S) i * y.s.f i = y.s.f i := fun i => by
      rw [frMapUniq_scal_one, _root_.one_mul]
    constructor
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).trans (ha i h)⟩
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).symm.trans (ha i h)⟩

end GlobalTheory.Frames
end

section

namespace GlobalTheory.ConjNegSquareNat

theorem conj_eq_neg_of_sq_eq_neg_nat {z : ℂ} {d : ℕ} (hd : (0 : ℕ) < d)
    (h : z ^ (2 : ℕ) = -(↑d : ℂ)) : (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  apply GlobalTheory.CMTypeOrConjugate.conj_eq_neg_of_sq <;> assumption

end GlobalTheory.ConjNegSquareNat
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDatumEq

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

end GlobalTheory.ShortDatumEq
end
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Translate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  ext i; simp [fv, TensorProduct.tmul_add]

lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  ext i; simp [fv]

lemma fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

lemma fv_smul (b : E) (x : Fin n → E) :
    fv F (b • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b : RA F E) • fv F x := by
  ext i; simp [fv]

lemma gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (a ⊗ₜ[F] x i : RA F E)) = (a ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by
  ext i; simp [fv]

lemma fv_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

lemma hat_smul_int {S : Set (Fin n → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    (a ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩
    ext i; simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma hat_smul_ring (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩
    ext i; simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def pre (M : Matrix (Fin n) (Fin n) (RA F E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) where
  carrier := {v | M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [fv_add, Matrix.mulVec_add]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [fv_zero, Matrix.mulVec_zero]; exact zero_mem _
  smul_mem' := by
    intro b x hx
    simp only [Set.mem_ofPred_eq] at *
    have : b • x = (b : E) • x := rfl
    rw [this, fv_smul, Matrix.mulVec_smul]
    exact hat_smul_ring L b hx

lemma mem_pre {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ pre M L ↔ M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E)) := Iff.rfl

lemma mulVec_mem_hat {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (Fin n → E)} (hS : S ⊆ pre M L) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, Matrix.mulVec_smul]
    exact hat_smul_int ha' (hS hx)
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

lemma exists_bound (M : Matrix (Fin n) (Fin n) (RA F E)) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (h : ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ hat F (L : Set (Fin n → E))) :
    ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  classical
  choose f hf0 hf using h
  obtain ⟨s, hs⟩ := hL
  refine ⟨∏ x ∈ s, f (M.mulVec (fv F x)), Finset.prod_pos fun _ _ => hf0 _, fun z hz => ?_⟩
  rw [← Matrix.smul_mulVec]
  refine mulVec_mem_hat ?_ hz
  have : L ≤ pre ((∏ x ∈ s, f (M.mulVec (fv F x))) • M) L := by
    conv_lhs => rw [← hs]
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec (fv F x))) (Finset.mem_coe.1 hx)
    rw [SetLike.mem_coe, mem_pre, Matrix.smul_mulVec, hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) _
  exact this

lemma nsmul_mem_hat {S S' : Set (Fin n → E)} {d : ℕ} (h : ∀ x ∈ S, d • x ∈ S') {z : Fin n → RA F E}
    (hz : z ∈ hat F S) : d • z ∈ hat F S' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_nsmul]
    exact hat_smul_int ha' (fv_mem_hat (h x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma nsmul_cancel {d : ℕ} (hd : 0 < d) {x y : Fin n → RA F E} (h : d • x = d • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
  have := congrArg (fun z => (d : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hd'] using this

end GlobalTheory.AdLat.Translate


open GlobalTheory.AdLat.Translate in
theorem GlobalTheory.AdLat.exists_lattice_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g hL hspan
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E))
    with hH
  have hGH : ∀ z, G.mulVec (H.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]
  have hHG : ∀ z, H.mulVec (G.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]
  have him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔
      H.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hHG]; exact hu
    · intro h; exact ⟨_, h, hGH z⟩
  obtain ⟨d, hd, hdG⟩ := exists_bound G hL h4
  obtain ⟨e, he, heH⟩ := exists_bound H hL h4
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : E) ≠ 0 := by exact_mod_cast he.ne'
  have hlow : ∀ x ∈ L, e • x ∈ pre H L := by
    intro x hx
    rw [mem_pre, fv_nsmul, Matrix.mulVec_smul]
    exact heH _ (fv_mem_hat hx)
  have hup : ∀ x ∈ pre H L, d • x ∈ L := by
    intro x hx
    rw [← h1, fv_nsmul, ← hGH (fv F x)]
    exact hdG _ hx
  refine ⟨pre H L, ?_, ?_, ?_, ?_⟩
  · ext v
    exact (him _).symm
  · have hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
      intro x y hxy
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at hxy
      exact smul_right_injective _ hd' hxy
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hup x hx
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact (isNoetherian_submodule.1 this) _ hle
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have hx' : x = (e : E)⁻¹ • (e • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))
  · ext z
    rw [him]
    constructor
    · intro hz
      exact mulVec_mem_hat subset_rfl hz
    · intro hz
      have hdz : d • z ∈ hat F (L : Set (Fin n → E)) := by
        rw [← hGH z]; exact hdG _ hz
      obtain ⟨x, -, w, hw, hxw⟩ := h2 (d * e) (Nat.mul_pos hd he) _ hdz
      have hx' : x = d • ((d : E)⁻¹ • x) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]
      have hz' : z = fv F ((d : E)⁻¹ • x) + e • w := by
        apply nsmul_cancel hd
        rw [smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]
      have hy : (d : E)⁻¹ • x ∈ pre H L := by
        rw [mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]
        exact sub_mem hz (heH _ hw)
      rw [hz']
      exact add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicCompletion_rational_points_and_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_rational_points_and_approx | exact GlobalTheory.AdLat.hat_rational_points_and_approx | (intros; apply GlobalTheory.AdLat.hat_rational_points_and_approx <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

theorem _root_.GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  exact @GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_mem_basicOpen_iff_of_isPullback {P X Y Z : Scheme.{0}} {pm : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z}
    {f : Y ⟶ Z} (hP : IsPullback pm g' g f) {J : Type} (U : J → X.Opens) (U' : J → P.Opens)
    (hU : ∀ i, U' i = pm ⁻¹ᵁ U i) (s : ∀ i, Γ(X, U i)) (s' : ∀ i, Γ(P, U' i))
    (hs : ∀ i, (pm.appLE _ _ (hU i).le).hom (s i) = s' i) (p' : Y) :
    (∃ (q : P) (i : J), g' q = p' ∧ q ∈ P.basicOpen (s' i)) ↔
      ∃ (q : X) (i : J), g q = f p' ∧ q ∈ X.basicOpen (s i) := by
  have key : ∀ (i : J) (q : P), q ∈ P.basicOpen (s' i) ↔ pm q ∈ X.basicOpen (s i) := by
    intro i q
    have e := Scheme.basicOpen_appLE pm (U' i) (U i) (hU i).le (s i)
    have e' : P.basicOpen (s' i) = U' i ⊓ pm ⁻¹ᵁ (X.basicOpen (s i)) := by
      rw [← hs i]; exact e
    rw [e']
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hU i]
    exact X.basicOpen_le (s i) h
  constructor
  · rintro ⟨q, i, rfl, hq⟩
    refine ⟨pm q, i, ?_, (key i q).1 hq⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP.w]
  · rintro ⟨q, i, hq, hq'⟩
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback hP q p' hq
    exact ⟨z, i, hz, (key i z).2 hq'⟩

theorem secBC_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x x' hx s s' hbc p'
  obtain ⟨pm, h1, h2, h3⟩ := hbc
  have hA : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left
      Xo.univ.t.G.hom x := (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have hB : IsPullback (snd (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      Xo.univ.t.G.hom x' := (IsPullback.of_hasPullback x' Xo.univ.t.G.hom).flip
  have hP : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) := by
    refine IsPullback.of_right ?_ h2 hA
    rw [h1]
    exact hx ▸ hB
  have hU : ∀ i : Fin 1 → Xo.univ.t.PP.L.ι, (PPx x').U i = pm ⁻¹ᵁ (PPx x).U i := by
    intro i
    ext y
    change y ∈ ⋂ k : Fin 1, (snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) ↔
      pm y ∈ ⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
    rw [← h1]
    simp only [Set.mem_iInter, Set.mem_preimage, Scheme.Hom.comp_apply]
  have h1' : ∀ i, scal x 1 i = 1 := fun i => by
    simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]
  refine exists_mem_basicOpen_iff_of_isPullback hP (PPx x).U (PPx x').U hU s.f s'.f (fun i => ?_) p'
  have := h3 i (hU i).le
  rwa [h1' i, _root_.one_mul] at this

end GlobalTheory.Frames
end

section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem exists_factor_openImmersion {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (j : Sp R ⟶ X)
    [IsOpenImmersion j] (x : Sp S ⟶ X) (p : Sp S) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] (lam : S →+* T), IsUnit (lam g) →
      ∃ ψ : R →+* T, spMap lam ≫ x = spMap ψ ≫ j := by
  have hU : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hU
  refine ⟨g, hpg, fun T _ lam hu => ?_⟩
  have hr : Set.range (spMap lam ≫ x) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap lam q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    exact hsub hq
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j (spMap lam ≫ x) hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem openChart_factor_near_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R), OpenChart j y₀ → ∀ (S : Type) [CommRing S] [Algebra c.F S] (xF : Sp S ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) → ∀ p : Sp S, xF p ∈ Set.range j → ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) → ∃ ψ : R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j := by
  intro E _ _ _ H Dw l Xo c R _ _ j y₀ hj S _ _ xF hx p hp
  haveI := hj.1
  obtain ⟨g, hg, h⟩ := exists_factor_openImmersion j xF p hp
  refine ⟨g, hg, fun T _ _ lam hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := h T lam.toRingHom hu
  have h2 := congrArg (· ≫ pullback.snd _ _) hψ
  simp only [Category.assoc] at h2
  rw [hx, hj.2.2, ← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ ψ with commutes' := fun a => ?_ }, hψ⟩
  have h4 := RingHom.congr_fun h3 a
  exact h4.symm.trans (lam.commutes a)

end GlobalTheory.Frames
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.typeFn_period_exist_moduli_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  first | exact @GlobalTheory.PeriodExists.typeFn_period_exist | exact GlobalTheory.PeriodExists.typeFn_period_exist | (intros; apply GlobalTheory.PeriodExists.typeFn_period_exist <;> assumption)
end
