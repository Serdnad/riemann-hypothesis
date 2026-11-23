module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle083
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem det_blocks_lower {S J : Type} [CommRing S] [Fintype J] [DecidableEq J] (m : J → ℕ)
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) (hz : ∀ τ i j, i < j → g τ i j = 0) {n : ℕ}
    (e : Fin n ≃ Σ τ : J, Fin (m τ)) :
    ((Matrix.blockDiagonal' g).submatrix e e).det = ∏ x : (Σ τ : J, Fin (m τ)), g x.1 x.2 x.2 := by
  rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun τ _ => Matrix.det_of_lowerTriangular _ fun i j hij => hz τ i j hij

theorem isCombAt_blocks {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {J : Type} [Fintype J] [DecidableEq J] {m : J → ℕ}
    (u : ∀ τ, Fin (m τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ τ i, IsTanAt x (u τ i))
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) {n : ℕ} (e : Fin n ≃ Σ τ : J, Fin (m τ)) (i : Fin n)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsCombAt x (u (e i).1) (g (e i).1 (e i).2) w) :
    IsCombAt x (fun j => u (e j).1 (e j).2) ((Matrix.blockDiagonal' g).submatrix e e i) w := by
  obtain ⟨N, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (hu τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  rw [hcomb] at h ⊢
  rw [h]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => Matrix.blockDiagonal' g (e i) p • b p.1 p.2), Fintype.sum_sigma]
  generalize e i = p
  obtain ⟨a, k⟩ := p
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro σ _ hσ
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hσ.symm, zero_smul, Finset.sum_const_zero]
  · simp

theorem rule_frBor : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g e K _ _ _ t y y' Φ Φ' hb hT hT'
  obtain ⟨M, hz, hd, hx, hc, hs⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  have fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → GlobalTheory.Frames.SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
    intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
    obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
    obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
    obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
    have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
      Φ'.th hx hn.symm hs hw hθ).1 ht'
    obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
    have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
      rintro _ rfl
      exact hu
    have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
      fun i => huv _
    have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
    have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
        rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
      rintro _ rfl _
      rfl
    refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
      fun a => ?_, ?_, hv⟩, fun i => ?_⟩
    · exact (hr _ n.base he).symm ▸ hw.2
    · refine Eq.trans ?_ (hm j i)
      have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
      rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · ext <;> simp [dualMap]
    · rw [← hn, ← Category.assoc, hv, Category.assoc]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    (t none : K) _ hsc hcomb
  have e3 := (det_blocks_lower (fun τ => Dw.mult τ) M hz e).trans (Finset.prod_congr rfl fun x _ => hd x.1 x.2)
  have e4 : ((t none : K)) ^ 8 * (κ K Φ'.key : K) =
      (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (t (some x) : K)) ^ 4 * (κ K Φ.key : K) := by
    refine e2.trans ?_
    exact congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1
  apply Units.ext
  have h0 : (t none : K) ≠ 0 := Units.ne_zero _
  rw [kch_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_prod]
  field_simp
  linear_combination e4

end GlobalTheory.KeyFourth
end

section

namespace GlobalTheory.HolArc

theorem isAlgebraic_of_etale (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Algebra.Etale S R] [FaithfulSMul S R] : Algebra.IsAlgebraic S R := by
  let K := FractionRing S
  let L := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : Algebra.FormallyEtale R L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  haveI : Algebra.EssFiniteType R L := .of_isLocalization L (nonZeroDivisors _)
  haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S R L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L
  haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S R L)
    (IsFractionRing.injective R L)

theorem faithfulSMul_of_flat (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Module.Flat S R] : FaithfulSMul S R := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have hreg : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
  have : a • (1 : R) = a • (0 : R) := by simp [Algebra.smul_def, ha]
  exact one_ne_zero (hreg this)

theorem exists_line (m : ℕ) (q : MvPolynomial (Fin m) ℂ) (hq : q ≠ 0) (b₀ : Fin m → ℂ) :
    ∃ (v : Fin m → ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → MvPolynomial.eval (b₀ + u • v) q ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (MvPolynomial.funext fun x => by simpa using h x)
  let v := w - b₀
  let Q : Polynomial ℂ := MvPolynomial.aeval
    (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) q
  have hQ : ∀ u, Q.eval u = MvPolynomial.eval (b₀ + u • v) q := fun u => by
    have : (Polynomial.evalRingHom u).comp
        (MvPolynomial.aeval (R := ℂ) (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) :
          MvPolynomial (Fin m) ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom =
        MvPolynomial.eval (b₀ + u • v) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp <;> ring
    exact congrArg (fun f : MvPolynomial (Fin m) ℂ →+* ℂ => f q) this
  have hQ0 : Q ≠ 0 := fun h => hw (by
    have := hQ 1
    simpa [h, v] using this.symm)
  have hfin : (((Q.roots.toFinset.erase 0 : Finset ℂ) : Set ℂ))ᶜ ∈ nhds (0 : ℂ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.1 hfin
  refine ⟨v, ρ, hρ, fun u hu hu0 h => hb hu ?_⟩
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Set.mem_singleton_iff, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQ, h]
  simpa using hu0

end GlobalTheory.HolArc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.HolArc

theorem exists_holPts_ne_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  intro F A _ _ _ _ hS ψ₀ p hp
  haveI := hS
  haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀
  obtain ⟨g, m, s, hg, het⟩ := SmoothPointFamily.exists_etale_away (R := F) (RingHom.ker ψ₀)
  have hg₀ : ψ₀ g ≠ 0 := hg
  have hgne : g ≠ 0 := fun h => hg₀ (by simp [h])
  let σ : F →+* ℂ := ψ₀.comp (algebraMap F A)
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hgne
  haveI : IsDomain R := IsLocalization.isDomain_localization hle
  have hι : Function.Injective ι := IsLocalization.injective R hle
  let e : R →+* ℂ := IsLocalization.Away.lift g (g := ψ₀) (isUnit_iff_ne_zero.2 hg₀)
  have he : ∀ a, e (ι a) = ψ₀ a := fun a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) F →+* R := MvPolynomial.eval₂Hom (algebraMap F R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap F A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply F A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have heC : ∀ k, e (P (MvPolynomial.C k)) = σ k := fun k => by rw [hPC, he]; rfl

  obtain ⟨c, hc0, hc⟩ : ∃ c : MvPolynomial (Fin m) F, c ≠ 0 ∧ ι p ∣ P c := by
    letI : Algebra (MvPolynomial (Fin m) F) R := P.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin m) F) R := het
    haveI : FaithfulSMul (MvPolynomial (Fin m) F) R := faithfulSMul_of_flat _ _
    haveI := isAlgebraic_of_etale (MvPolynomial (Fin m) F) R
    exact (Algebra.IsAlgebraic.isAlgebraic (ι p)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff ι hι).2 hp))
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m F R P Set.univ (fun _ => σ) 0 e het
      isOpen_univ trivial (fun a => differentiableOn_const _) heC
  obtain ⟨h3, h4⟩ := hrec 0 e heC hO₀
  simp only [hPX, he] at h3 h4
  let b₀ : Fin m → ℂ := fun i => ψ₀ (s i)
  have hq0 : MvPolynomial.map σ c ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ σ.injective)).2 hc0
  obtain ⟨v, ρ, hρ, hline⟩ := exists_line m (MvPolynomial.map σ c) hq0 b₀
  let ℓ : ℂ → (Fin 0 → ℂ) × (Fin m → ℂ) := fun u => (0, b₀ + u • v)
  have hℓd : Differentiable ℂ ℓ :=
    (differentiable_const _).prodMk ((differentiable_const _).add (differentiable_id.smul_const v))
  have hℓ0 : ℓ 0 = (0, b₀) := by simp [ℓ]
  have hNo : ℓ ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (hN.preimage hℓd.continuous).mem_nhds (by simpa only [Set.mem_preimage, hℓ0] using h3)
  obtain ⟨ρ', hρ', hb⟩ := Metric.mem_nhds_iff.1 hNo
  have hsub : ∀ u ∈ Metric.ball (0 : ℂ) (min ρ ρ'), ℓ u ∈ N := fun u hu =>
    hb (Metric.ball_subset_ball (min_le_right _ _) hu)
  refine ⟨fun u => (τ (ℓ u)).comp ι, min ρ ρ', ⟨lt_min hρ hρ', fun a => ?_⟩, ?_, fun u hu => ?_,
    fun u hu hu0 h => ?_⟩
  · exact (hd (ι a)).comp hℓd.differentiableOn hsub
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, hℓ0]
    rw [show ((0 : Fin 0 → ℂ), b₀) = (0, fun i => ψ₀ (s i)) from rfl, h4, he]
  · refine RingHom.ext fun k => ?_
    simp only [RingHom.comp_apply]
    rw [← hPC]
    exact (hτ _ (hsub u hu)).2.1 k
  · have hev : (τ (ℓ u)).comp P = (MvPolynomial.eval (b₀ + u • v)).comp (MvPolynomial.map σ) := by
      refine MvPolynomial.ringHom_ext (fun k => ?_) fun i => ?_
      · simpa using (hτ _ (hsub u hu)).2.1 k
      · simpa [ℓ] using (hτ _ (hsub u hu)).2.2 i
    obtain ⟨d, hd'⟩ := hc
    have h0 : τ (ℓ u) (P c) = 0 := by
      rw [hd', map_mul]
      exact mul_eq_zero_of_left h _
    have h1 := congrArg (fun f : MvPolynomial (Fin m) F →+* ℂ => f c) hev
    simp only [RingHom.comp_apply] at h1
    exact hline u (Metric.ball_subset_ball (min_le_left _ _) hu) hu0 (h1.symm.trans h0)

end GlobalTheory.HolArc
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem tied_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  open GlobalTheory GlobalTheory.CM GlobalTheory.Frames MonoidalCategory CartesianMonoidalCategory MonObj IsDedekindDomain MeasureTheory in
  intro E _ _ _ H Dw l Xo c g e S S' _ _ _ _ _ φ y z Φ Φ' hm ⟨ht, hg1, hv1⟩ ⟨ht', hg2, hv2⟩
  obtain ⟨hx, hu, hs⟩ := ((GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S' φ y).2.2 z).1 hm
  obtain ⟨hg, v', hv', hk, hv⟩ := GlobalTheory.LamT.fibKey_keyPB E H Dw l Xo S S' φ.toRingHom y.x z.x Φ Φ' y.s z.s hx ht ht' hs
  have hvv : v' = Φ'.v := by
    funext i
    apply Over.OverMorphism.ext
    apply Φ'.m.cart.1.hom_ext
    · rw [hv i, hv1, hv2, hu]
      rfl
    · rw [Over.w, Over.w]
  subst hvv
  exact hk

end GlobalTheory.KeyFourth
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

end GlobalTheory.HTPres
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section


open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LineNorm.isTanBasis_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x e cf u) → GlobalTheory.LineNorm.IsTanBasis t x e := by
  intro E _ _ _ H X t R _ x g e he hb
  let v : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun i => tanOf (he i)
  have hv : Full v := fun n => (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff v a n).1 (hb _ (isTan_tv n))
  refine ⟨he, fun S _ φ w hw => ?_⟩
  have h := full_bc φ hv (tanOf hw)
  exact (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff (fun i => resM φ (v i)) a (tanOf hw)).2 h
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem smooth_cbase {X : Scheme.{0}} {T : Type} [Finite T] (m : T → ℕ) (U : X.affineOpens) : Smooth (cbase m U) := by
  have h : Smooth (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth Γ(X, U.1) (MvPolynomial (CellVar m) Γ(X, U.1)))
  have h' : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h'' : Smooth U.2.fromSpec := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _ h h''

theorem cell_smooth_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  intro X _ T _ m U hX
  have := smooth_cbase m U
  exact ⟨this, forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (cbase m U) hX⟩

end GlobalTheory.FlagEmb
end
